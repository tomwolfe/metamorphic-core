# src/core/llm_orchestration.py
import os
import re
import logging
from enum import Enum
from typing import Optional, List, TYPE_CHECKING
import google.genai
from huggingface_hub import InferenceClient

# Moved these imports to the top to resolve NameError for CodeChunk
from src.core.chunking.dynamic_chunker import SemanticChunker, CodeChunk
from src.core.chunking.recursive_summarizer import RecursiveSummarizer

from src.utils.config import SecureConfig, ConfigError
from pydantic import BaseModel, ValidationError
from src.core.context_manager import parse_code_chunks
from src.core.monitoring import Telemetry
from src.core.verification import (
    FormalVerificationError,
    InvalidCodeHashError,
    MaxSummaryRetriesError,
    ModelCapacityError,
    CriticalFailure,
)
from collections import defaultdict
import time
import threading
from src.core.optimization.adaptive_token_allocator import TokenAllocator
from src.core.knowledge_graph import KnowledgeGraph, Node
from src.core.optimization.token_optimizer import TokenOptimizer
from src.core.verification.specification import FormalSpecification
from src.core.verification.decorators import formal_proof

from tenacity import Retrying, stop_after_attempt, wait_exponential, RetryError

logger = logging.getLogger(__name__)

class LLMProvider(str, Enum):
    GEMINI = "gemini"
    HUGGING_FACE = "huggingface"

class LLMConfig(BaseModel):
    provider: LLMProvider
    gemini_api_key: Optional[str] = None
    hf_api_key: Optional[str] = None
    max_retries: int = 3
    timeout: int = 30
    # Updated default Hugging Face model to Qwen/Qwen3-235B-A22B
    hugging_face_model: str = SecureConfig.get("HUGGING_FACE_MODEL", "Qwen/Qwen3-235B-A22B")
    enable_hugging_face: bool = True # Default to True, will be overridden by SecureConfig

class LLMOrchestrator:
    def __init__(self):
        self.client = None
        self.active_provider = None
        self.hf_client = None
        self.hf_model_name = None
        self.config = self._load_config()
        self._configure_providers()
        self._last_gemini_call_start_time = 0.0
        self._gemini_call_lock = threading.Lock()
        self._GEMINI_MIN_INTERVAL_SECONDS = 6.0
        self.telemetry = Telemetry()

    def _load_config(self) -> LLMConfig:
        try:
            SecureConfig.load() # Ensures all configs including API keys are validated/loaded
            return LLMConfig(
                provider=LLMProvider(SecureConfig.get("LLM_PROVIDER", "gemini")),
                gemini_api_key=SecureConfig.get("GEMINI_API_KEY"),
                hf_api_key=SecureConfig.get("HUGGING_FACE_API_KEY"),
                hugging_face_model=SecureConfig.get("HUGGING_FACE_MODEL", "Qwen/Qwen3-235B-A22B"),
                max_retries=SecureConfig.get("LLM_MAX_RETRIES", 3), # Will be int due to default
                timeout=SecureConfig.get("LLM_TIMEOUT", 30),       # Will be int due to default
                enable_hugging_face=SecureConfig.get("ENABLE_HUGGING_FACE", True) # Will be bool
            )
        except (ValidationError, ConfigError, ValueError) as e:
            logger.error(f"Error loading LLM configuration: {str(e)}")
            raise RuntimeError(f"Invalid LLM configuration: {str(e)}")

    def _configure_providers(self):
        if self.config.provider == LLMProvider.GEMINI:
            if not self.config.gemini_api_key:
                raise RuntimeError("GEMINI_API_KEY is required for Gemini provider")
            self.client = google.genai.Client(api_key=self.config.gemini_api_key)
            self.client.model = "gemini-2.5-flash"
            self.client.api_key = self.config.gemini_api_key
            logger.info(f"Primary LLM_PROVIDER is Gemini. Main client configured for model: {self.client.model}")
        elif self.config.provider == LLMProvider.HUGGING_FACE:
            if not self.config.hf_api_key:
                raise RuntimeError("HUGGING_FACE_API_KEY is required for Hugging Face provider")
            # Explicitly set provider to "hf-inference" to ensure the correct backend
            # and avoid issues with default provider detection.
            self.client = InferenceClient(
                provider="hf-inference",
                token=self.config.hf_api_key,
                model=self.config.hugging_face_model,
            )
            self.hf_model_name = self.config.hugging_face_model
            logger.info(f"Primary LLM_PROVIDER is Hugging Face. Main client configured for model: {self.config.hugging_face_model}")
        else:
            raise ValueError(f"Unsupported LLM provider: {self.config.provider}")

        # Conditionally configure a separate hf_client
        if self.config.enable_hugging_face:
            if self.config.hf_api_key and self.config.hugging_face_model:
                try:
                    self.hf_client = InferenceClient(
                        provider="hf-inference",
                        token=self.config.hf_api_key,
                        model=self.config.hugging_face_model
                    )
                    self.hf_model_name = self.config.hugging_face_model # Store the actual model name used
                    logger.info(f"Dedicated Hugging Face client configured for model: {self.hf_model_name}")
                except Exception as e:
                    logger.warning(f"Failed to initialize dedicated Hugging Face client: {e}. HF models may not be available.")
            else:
                logger.warning("Hugging Face API key or model name not configured. Dedicated HF client not initialized.")
        else:
            logger.info("Hugging Face client is disabled by configuration (ENABLE_HUGGING_FACE=false).")
            self.hf_client = None
            self.hf_model_name = None

    def _apply_gemini_rate_limit(self):
        """Ensures calls to Gemini API do not exceed the rate limit."""
        if self.config.provider == LLMProvider.GEMINI:
            with self._gemini_call_lock:
                current_time = time.monotonic()
                elapsed_since_last_call = current_time - self._last_gemini_call_start_time

                if elapsed_since_last_call < self._GEMINI_MIN_INTERVAL_SECONDS:
                    sleep_duration = self._GEMINI_MIN_INTERVAL_SECONDS - elapsed_since_last_call
                    logger.info(f"Gemini rate limit: sleeping for {sleep_duration:.2f} seconds.")
                    time.sleep(sleep_duration)
                self._last_gemini_call_start_time = time.monotonic()

    def generate(self, prompt: str) -> str:
        return self._generate_with_retry(prompt)

    def _generate_with_retry(self, prompt: str, model: Optional[str] = None) -> str:
        """
        Generates content from the LLM with rate limiting and robust retries.
        """
        if model is None:
            model = self.config.provider.value

        try:
            retrying = Retrying(
                stop=stop_after_attempt(self.config.max_retries + 1),
                wait=wait_exponential(multiplier=1, min=2, max=10),
                reraise=False
            )
            return retrying(self._call_llm_api, prompt, model)

        except RetryError as e:
            logger.error(f"LLM API failed after all retries for prompt (first 200 chars): {prompt[:200]}. Last error: {e.last_attempt.exception()}")
            raise RuntimeError(f"LLM API failed after all retries: {e.last_attempt.exception()}") from e
        except Exception as e:
            logger.error(f"LLM API failed with non-retryable error for prompt (first 200 chars): {prompt[:200]}. Error: {str(e)}")
            raise RuntimeError(f"LLM API failed: {str(e)}") from e

    def _call_llm_api(self, text: str, model: str) -> str:
        """Directly call the appropriate LLM API based on the provider string.
        Rate limiting is applied here before each attempt.
        """
        self._apply_gemini_rate_limit()

        self.telemetry.track("model_usage", tags={"model": model})
        if model == LLMProvider.GEMINI.value:
            return self._gemini_generate(text)
        elif model == LLMProvider.HUGGING_FACE.value or model == self.config.hugging_face_model:
            return self._hf_generate(text)
        else:
            logger.error(f"Attempted to call unsupported model: {model} in LLMOrchestrator._call_llm_api")
            raise ValueError(f"Unsupported model: {model}")

    def _gemini_generate(self, prompt: str) -> str:
        try:
            # --- START OF CHANGE ---
            generation_config = google.genai.types.GenerationConfig(
                temperature=0.6,
                top_p=0.95,
                max_output_tokens=8192  # <-- ADD THIS LINE
            )
            response = self.client.models.generate_content(
                model=self.client.model,
                contents=prompt,
                generation_config=generation_config, # <-- USE THE NEW CONFIG OBJECT
            )
            # --- END OF CHANGE ---
            if response.candidates and response.candidates[0].content and response.candidates[0].content.parts:
                parts = response.candidates[0].content.parts
                return "".join(part.text for part in parts if hasattr(part, "text"))
            logger.warning(f"Gemini API returned an empty or unexpected response structure for prompt (first 200 chars): {prompt[:200]}")
            return ""
        except Exception as e:
            logger.error(f"Gemini error during API call for prompt (first 200 chars): {prompt[:200]}. Error: {str(e)}")
            raise RuntimeError(f"Gemini error: {str(e)}")

    def _hf_generate(self, prompt: str) -> str:
        if not self.hf_client:
            logger.error("Hugging Face client not initialized. Cannot generate with Hugging Face model.")
            raise RuntimeError("Hugging Face client not initialized. Check HUGGING_FACE_API_KEY and HUGGING_FACE_MODEL settings.")
        
        hf_model_to_use = self.hf_model_name or self.config.hugging_face_model

        # Qwen3 recommended parameters for thinking mode
        temperature = 0.6
        top_p = 0.95
        max_tokens = 32768 # Recommended output length

        try:
            logger.debug(f"Calling Hugging Face chat completions API for model: {hf_model_to_use}")
            completion = self.hf_client.chat.completions.create(
                model=hf_model_to_use,
                messages=[{"role": "user", "content": prompt}],
                temperature=temperature,
                top_p=top_p,
                max_tokens=max_tokens,
                # stop=["</s>"], # Optional, if needed for Qwen3
            )
            
            response_content = completion.choices[0].message.content
            
            # Parse Qwen3 thinking content if present, with resilience
            thinking_content = ""
            actual_content = response_content
            
            if "<think>" in response_content:
                if "</think>" in response_content:
                    # Partition ensures we get content even if <think> is at the start or end
                    parts = response_content.split("</think>", 1)
                    think_block_part = parts[0]
                    actual_content = parts[1].strip() if len(parts) > 1 else ""
                    
                    # Remove the opening <think> tag
                    if think_block_part.startswith("<think>"):
                        thinking_content = think_block_part[len("<think>"):].strip()
                    else: # Should not happen if </think> was found and response starts with <think>
                        thinking_content = think_block_part.strip()
                        logger.warning("Found </think> but opening <think> tag was malformed or missing.")
                    
                    logger.debug(f"HF Thinking Content (Qwen3): {thinking_content if thinking_content else '<empty>'}")
                else:
                    logger.warning("Detected '<think>' tag without a closing '</think>' tag. Treating full response as content.")
            
            return actual_content

        except Exception as e:
            hf_model_name_for_log = hf_model_to_use or "Unknown HF Model"
            logger.error(f"Hugging Face chat completions error (model: {hf_model_name_for_log}): {str(e)}", exc_info=True)
            raise RuntimeError(f"Hugging Face chat completions error (model: {hf_model_name_for_log}): {str(e)}") from e

    def _count_tokens(self, text: str) -> int:
        # Simple token count for demonstration; replace with a proper tokenizer if needed
        return len(text.split())

class EnhancedLLMOrchestrator(LLMOrchestrator):
    def __init__(
        self, kg: KnowledgeGraph, spec: FormalSpecification, ethics_engine: "EthicalGovernanceEngine"
    ):
        super().__init__()
        self.chunker = SemanticChunker()
        self.allocator = TokenAllocator(total_budget=50000)
        self.summarizer = RecursiveSummarizer(self, spec, self.telemetry)
        self.kg = kg
        self.spec = spec
        self.ethics_engine = ethics_engine
        self.fallback_strategy = [
            self._primary_processing,
            self._secondary_model,
            self._third_model,
            self._recursive_summarization_strategy,
        ]
        self.optimizer = TokenOptimizer()

    def generate(self, prompt: str) -> str:
        self.telemetry.start_session()
        try:
            with self.telemetry.span("generate_logic"):
                if self._count_tokens(prompt) > 8000:
                    code = self._handle_large_context(prompt)
                else:
                    model = self.config.provider.value
                    code = super()._generate_with_retry(prompt, model=model)

            verification_result = self.spec.verify_predictions(code)
            if not verification_result.get("verified", False):
                raise FormalVerificationError("Formal verification failed for generated code")

            return code
        except FormalVerificationError as e:
            self.telemetry.track("error", tags={"type": "FormalVerificationError", "message": str(e)})
            raise
        except Exception as e:
            self.telemetry.track("error", tags={"type": "GenericError", "message": str(e)})
            raise
        finally:
            self.telemetry.publish()

    def _handle_large_context(self, prompt: str) -> str:
        chunks = self.chunker.chunk(prompt)
        if not hasattr(self.spec, 'validate_chunks') or not self.spec.validate_chunks(chunks):
             logger.warning("FormalSpecification does not have validate_chunks or validation failed.")
             if hasattr(self.spec, 'validate_chunks'):
                 self.telemetry.track("constraint_violation", tags={"constraint": "InitialChunkValidation"})
                 raise FormalVerificationError("Initial chunk validation failed")

        allocation = self.allocator.allocate(chunks, self._get_model_costs())
        summaries = []

        for idx, chunk in enumerate(chunks):
            with self.telemetry.span(f"chunk_{idx}"):
                if not hasattr(self.spec, 'verify') or not self.spec.verify(chunk):
                    logger.warning(f"FormalSpecification does not have verify or verification failed for chunk {idx}.")
                    if hasattr(self.spec, 'verify'):
                        self.telemetry.track("verification_failure", tags={"chunk_id": str(chunk.id)})
                        raise InvalidCodeHashError(f"Chunk {idx} failed verification")

                summary = self._process_chunk(chunk, allocation[idx])

                chunk_node_id = self.kg.add_node(Node(type="code_chunk", content=chunk.content, metadata={"chunk_id": str(getattr(chunk, 'id', f'chunk_{idx}'))}))

                summary_node = Node(
                    type="code_summary", content=summary, metadata={"source_chunk_id": str(chunk_node_id)}
                )
                summary_node_id = self.kg.add_node(summary_node)
                self.kg.add_edge(chunk_node_id, summary_node_id, "has_summary")
                summaries.append(summary)

        if not hasattr(self.summarizer, 'synthesize'):
             logger.error("RecursiveSummarizer missing synthesize method.")
             raise CriticalFailure("Summarization synthesis method missing.")

        return self.summarizer.synthesize(summaries)

    def _get_model_costs(self):
        costs = {
            "gemini": {"effective_length": 500000, "cost_per_token": 0.000001}
        }
        if self.hf_model_name: # This is set only if HF is enabled and client initialized
            costs[self.hf_model_name] = {"effective_length": 4096, "cost_per_token": 0.000002}
        return costs

    def _process_chunk(self, chunk: CodeChunk, allocation: tuple) -> str:
        tokens, model = allocation
        last_exception = None
        for strategy in self.fallback_strategy:
            with self.telemetry.span(f"strategy_{strategy.__name__}"):
                try:
                    result = strategy(chunk, tokens, model)
                    self.telemetry.track(
                        "model_success", tags={"model": model, "strategy": strategy.__name__}
                    )
                    return result
                except Exception as e:
                    self.telemetry.track(
                        "model_fallback", tags={"model": model, "strategy": strategy.__name__, "error": str(e)}
                    )
                    last_exception = e
                    logging.warning(f"Fallback strategy {strategy.__name__} failed: {e}")

        if last_exception:
            raise CriticalFailure(f"All processing strategies failed. Last exception: {last_exception}")
        else:
            raise CriticalFailure("All processing strategies failed, reason unknown.")

    @formal_proof(
        """
Lemma fallback_termination:
    forall chunk, exists n, strategy_n(chunk) terminates
""",
        autospec=True,
    )
    def _primary_processing(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        optimized = self.optimizer.optimize(chunk.content, tokens)
        return self._call_llm_api(optimized, model)

    def _secondary_model(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        if tokens < 500:
            raise ModelCapacityError("Insufficient tokens for secondary model")
        reduced_tokens = int(tokens * 0.75)
        optimized = self.optimizer.optimize(chunk.content, reduced_tokens)
        return self._call_llm_api(optimized, model)

    def _third_model(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        optimized = self.optimizer.aggressive_optimize(chunk.content, int(tokens * 0.5))
        return self._call_llm_api(optimized, model)

    def _recursive_summarization_strategy(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        if tokens < 1000:
            raise ModelCapacityError("Insufficient tokens for summarization")
        return self.summarizer.summarize_code_recursively(chunk.content)

    def _call_llm_api(self, text: str, model: str) -> str:
        return super()._call_llm_api(text, model)

def _count_tokens(self, text: str) -> int:
    return len(text.split())

def format_math_prompt(question: str) -> str:
    return f"""Please reason step by step and put your final answer within \\boxed{{}}.
Question: {question}
Answer: """

def extract_boxed_answer(text: str) -> str:
    match = re.search(r"\\boxed{([^}]+)}", text)
    if match:
        return match.group(1)