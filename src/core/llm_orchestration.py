# src/core/llm_orchestration.py
import os
import re
import logging
from enum import Enum
from typing import Optional, List, TYPE_CHECKING
import google.genai as genai
from huggingface_hub import InferenceClient
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
from src.core.chunking.recursive_summarizer import RecursiveSummarizer
from src.core.chunking.dynamic_chunker import SemanticChunker, CodeChunk
from src.core.optimization.adaptive_token_allocator import TokenAllocator
from src.core.knowledge_graph import KnowledgeGraph, Node
from src.core.optimization.token_optimizer import TokenOptimizer # Import TokenOptimizer
from src.core.verification.specification import FormalSpecification
from src.core.verification.decorators import formal_proof

from tenacity import Retrying, stop_after_attempt, wait_exponential, RetryError # Changed import to Retrying

# Ensure logger is defined if not already
logger = logging.getLogger(__name__) # FIX: Use __name__ for module-level logger

class LLMProvider(str, Enum):
    GEMINI = "gemini"
    HUGGING_FACE = "huggingface"

class LLMConfig(BaseModel):
    provider: LLMProvider
    gemini_api_key: Optional[str] = None
    hf_api_key: Optional[str] = None
    max_retries: int = 3
    timeout: int = 30
    hugging_face_model: str = SecureConfig.get("HUGGING_FACE_MODEL", "deepseek-ai/DeepSeek-R1-Distill-Qwen-32B")

class LLMOrchestrator:
    def __init__(self): # FIX: Correct method name from init to __init__
        self.client = None
        self.active_provider = None
        self.hf_client = None # Add dedicated Hugging Face client
        self.hf_model_name = None # Store the configured HF model name
        self.config = self._load_config()
        self._configure_providers()
        # --- ADD RATE LIMITING ATTRIBUTES ---
        # Track the time the last Gemini call started (or finished, consistently)
        self._last_gemini_call_start_time = 0.0 # Use float for time.monotonic()
        self._gemini_call_lock = threading.Lock() # Use a lock for thread safety
        self._GEMINI_MIN_INTERVAL_SECONDS = 6.0 # 60 seconds / 10 requests (10 RPM for Gemini Flash free tier)
        # --- END ADD ---
        # FIX: Initialize telemetry in base class if it's used there
        self.telemetry = Telemetry()


    def _load_config(self) -> LLMConfig:
        try:
            SecureConfig.load()
            return LLMConfig(
                provider=LLMProvider(SecureConfig.get("LLM_PROVIDER", "gemini")),
                gemini_api_key=SecureConfig.get("GEMINI_API_KEY"),
                hf_api_key=SecureConfig.get("HUGGING_FACE_API_KEY"),
                hugging_face_model=SecureConfig.get("HUGGING_FACE_MODEL", "deepseek-ai/DeepSeek-R1-Distill-Qwen-32B"),
                max_retries=int(SecureConfig.get("LLM_MAX_RETRIES", 3)),
                timeout=int(SecureConfig.get("LLM_TIMEOUT", 30)),
            )
        except (ValidationError, ConfigError, ValueError) as e:
            logger.error(f"Error loading LLM configuration: {str(e)}") # FIX: Use module-level logger
            raise RuntimeError(f"Invalid LLM configuration: {str(e)}")

    def _configure_providers(self):
        if self.config.provider == LLMProvider.GEMINI:
            if not self.config.gemini_api_key:
                raise RuntimeError("GEMINI_API_KEY is required for Gemini provider")
            # Initialize the client instance
            self.client = genai.Client(api_key=self.config.gemini_api_key)
            # Set model and api_key attributes on the instance
            self.client.model = "gemini-2.5-flash-preview-05-20" # CHANGED THIS LINE
            self.client.api_key = self.config.gemini_api_key # Redundant but harmless if already set by Client()
            logger.info(f"Primary LLM_PROVIDER is Gemini. Main client configured for model: {self.client.model}")
        elif self.config.provider == LLMProvider.HUGGING_FACE:
            if not self.config.hf_api_key:
                raise RuntimeError("HUGGING_FACE_API_KEY is required for Hugging Face provider")
            self.client = InferenceClient(
                token=self.config.hf_api_key,
                model=self.config.hugging_face_model,
            )
            self.hf_model_name = self.config.hugging_face_model # Store configured HF model name
            logger.info(f"Primary LLM_PROVIDER is Hugging Face. Main client configured for model: {self.config.hugging_face_model}")
        else:
            raise ValueError(f"Unsupported LLM provider: {self.config.provider}")

        # Additionally, always try to configure a separate hf_client if keys are available
        # This allows using HF models even if the primary provider is Gemini.
        if self.config.hf_api_key and self.config.hugging_face_model:
            try:
                self.hf_client = InferenceClient(token=self.config.hf_api_key, model=self.config.hugging_face_model)
                self.hf_model_name = self.config.hugging_face_model # Ensure hf_model_name is set
                logger.info(f"Dedicated Hugging Face client configured for model: {self.config.hugging_face_model}")
            except Exception as e:
                logger.warning(f"Failed to initialize dedicated Hugging Face client: {e}. HF models may not be available if primary provider is not HF.")

    # --- ADD NEW METHOD FOR GEMINI RATE LIMITING ---
    def _apply_gemini_rate_limit(self):
        """Ensures calls to Gemini API do not exceed the rate limit."""
        if self.config.provider == LLMProvider.GEMINI:
            # Acquire the lock to ensure only one thread checks/updates the time at once
            with self._gemini_call_lock:
                current_time = time.monotonic()
                elapsed_since_last_call = current_time - self._last_gemini_call_start_time

                if elapsed_since_last_call < self._GEMINI_MIN_INTERVAL_SECONDS:
                    sleep_duration = self._GEMINI_MIN_INTERVAL_SECONDS - elapsed_since_last_call
                    logger.info(f"Gemini rate limit: sleeping for {sleep_duration:.2f} seconds.") # FIX: Use module-level logger
                    time.sleep(sleep_duration)
                # Update the last call start time *after* potential sleep and before the API call
                # This marks the start of the current API call's interval.
                self._last_gemini_call_start_time = time.monotonic()
    # --- END ADD ---

    def generate(self, prompt: str) -> str:
        return self._generate_with_retry(prompt)

    def _generate_with_retry(self, prompt: str, model: Optional[str] = None) -> str:
        """
        Generates content from the LLM with rate limiting and robust retries.
        """
        # If model is not explicitly provided, use the configured primary provider
        if model is None:
            model = self.config.provider.value

        try:
            # Create a retry mechanism dynamically using instance config
            # stop_after_attempt(self.config.max_retries + 1) means:
            # if max_retries = 3, then 3 retries + 1 initial attempt = 4 total attempts.
            retrying = Retrying(
                stop=stop_after_attempt(self.config.max_retries + 1),
                wait=wait_exponential(multiplier=1, min=2, max=10),
                reraise=False # FIX: Change to False so RetryError is always raised on failure
            )

            # Call the _call_llm_api method via the tenacity Retrying object.
            # _apply_gemini_rate_limit is now called inside _call_llm_api before each attempt.
            return retrying(self._call_llm_api, prompt, model)

        except RetryError as e:
            # This exception is raised by tenacity if all attempts fail.
            logger.error(f"LLM API failed after all retries for prompt (first 200 chars): {prompt[:200]}. Last error: {e.last_attempt.exception()}") # FIX: Use module-level logger
            raise RuntimeError(f"LLM API failed after all retries: {e.last_attempt.exception()}") from e
        except Exception as e:
            # Catch other non-retryable exceptions (e.g., invalid API key, malformed request before API call).
            # This block should now only catch exceptions that are NOT wrapped by tenacity (e.g., if _call_llm_api is called directly outside retrying)
            logger.error(f"LLM API failed with non-retryable error for prompt (first 200 chars): {prompt[:200]}. Error: {str(e)}") # FIX: Use module-level logger
            raise RuntimeError(f"LLM API failed: {str(e)}") from e

    # --- MODIFIED: _call_llm_api no longer has @retry decorator ---
    def _call_llm_api(self, text: str, model: str) -> str:
        """Directly call the appropriate LLM API based on the provider string.
        Rate limiting is applied here before each attempt.
        """
        # Apply rate limit before each actual API attempt.
        # This method is a no-op for non-Gemini providers.
        self._apply_gemini_rate_limit() # <--- MOVED HERE

        self.telemetry.track("model_usage", tags={"model": model}) # Moved from EnhancedLLMOrchestrator
        if model == LLMProvider.GEMINI.value:
            return self._gemini_generate(text)
        elif model == LLMProvider.HUGGING_FACE.value or model == self.config.hugging_face_model:
             # Allow calling with 'huggingface' or the specific model name
            return self._hf_generate(text)
        # Add other models if explicitly supported here in the base class
        # elif model == "some_other_model":
        #     return self._some_other_generate(text)
        else:
            logger.error(f"Attempted to call unsupported model: {model} in LLMOrchestrator._call_llm_api") # FIX: Use module-level logger
            raise ValueError(f"Unsupported model: {model}")
    # --- END MODIFIED ---


    def _gemini_generate(self, prompt: str) -> str:
        # Rate limiting is now applied in _call_llm_api before this method is called.
        # This method should only contain the direct API call logic
        try:
            # Use the model attribute set during configuration
            response = self.client.models.generate_content(
                model=self.client.model, # Use the configured model
                contents=prompt,
                config=genai.types.GenerateContentConfig(
                    temperature=0.6,
                    top_p=0.95,
                ),
            )
            if response.candidates and response.candidates[0].content and response.candidates[0].content.parts:
                parts = response.candidates[0].content.parts
                return "".join(part.text for part in parts if hasattr(part, "text"))
            # Handle cases where response might be empty or malformed without raising an exception
            logger.warning(f"Gemini API returned an empty or unexpected response structure for prompt (first 200 chars): {prompt[:200]}") # FIX: Use module-level logger
            return ""
        except Exception as e:
            # Log the prompt that caused the error for easier debugging
            logger.error(f"Gemini error during API call for prompt (first 200 chars): {prompt[:200]}. Error: {str(e)}") # FIX: Use module-level logger
            # Re-raise to be handled by _generate_with_retry
            raise RuntimeError(f"Gemini error: {str(e)}")


    def _hf_generate(self, prompt: str) -> str:
        # This method should only contain the direct API call logic
        if not self.hf_client:
            logger.error("Hugging Face client not initialized. Cannot generate with Hugging Face model.")
            raise RuntimeError("Hugging Face client not initialized. Check HUGGING_FACE_API_KEY and HUGGING_FACE_MODEL settings.")
        try:
            # Use the dedicated hf_client instance
            return self.hf_client.text_generation(
                prompt,
                max_new_tokens=2048,
                temperature=0.6,
                top_p=0.95,
                repetition_penalty=1.2,
                do_sample=True,
                seed=42,
                stop_sequences=["</s>"],
                return_full_text=False
            )
        except Exception as e:
            # Use self.hf_model_name if available, otherwise fallback
            hf_model_name_for_log = self.hf_model_name or "Unknown HF Model"
            logger.error(f"Hugging Face error (model: {hf_model_name_for_log}): {str(e)}", exc_info=True)
            raise RuntimeError(f"Hugging Face error (model: {hf_model_name_for_log}): {str(e)}") from e

    def _count_tokens(self, text: str) -> int:
        # Simple token count for demonstration; replace with a proper tokenizer if needed
        return len(text.split())
class EnhancedLLMOrchestrator(LLMOrchestrator):
    def __init__( # FIX: Correct method name from init to __init__
        self, kg: KnowledgeGraph, spec: FormalSpecification, ethics_engine: "EthicalGovernanceEngine"
    ):
        super().__init__()
        # self.telemetry = Telemetry() # REMOVED: telemetry is now initialized in the base class
        self.chunker = SemanticChunker()
        self.allocator = TokenAllocator(total_budget=50000)
        # Pass self (the Enhanced instance) to RecursiveSummarizer
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
        # FIX: Initialize optimizer here, as it's used by fallback strategies
        self.optimizer = TokenOptimizer()


    def generate(self, prompt: str) -> str:
        self.telemetry.start_session()
        try:
            with self.telemetry.span("generate_logic"):
                # Increased threshold to trigger large context handling
                if self._count_tokens(prompt) > 8000: # Increased threshold
                    code = self._handle_large_context(prompt)
                else:
                    model = self.config.provider.value
                    # Call the generate method from the base class (which includes retry and rate limit)
                    # The base generate calls _generate_with_retry, which calls _call_llm_api
                    code = super()._generate_with_retry(prompt, model=model) # Explicitly pass model

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
        # Assuming spec has a validate_chunks method
        if not hasattr(self.spec, 'validate_chunks') or not self.spec.validate_chunks(chunks):
             # Log or handle the case where validate_chunks is missing or fails
             logger.warning("FormalSpecification does not have validate_chunks or validation failed.") # FIX: Use module-level logger
             # Decide how to proceed: raise error, skip validation, etc.
             # For now, let's assume it should raise an error if validation fails
             if hasattr(self.spec, 'validate_chunks'):
                 self.telemetry.track("constraint_violation", tags={"constraint": "InitialChunkValidation"})
                 raise FormalVerificationError("Initial chunk validation failed")
             # If validate_chunks is missing, maybe just log and continue? Depends on requirements.
             # raise FormalVerificationError("FormalSpecification missing validate_chunks method")


        allocation = self.allocator.allocate(chunks, self._get_model_costs())
        summaries = []

        for idx, chunk in enumerate(chunks):
            with self.telemetry.span(f"chunk_{idx}"):
                # Assuming spec has a verify method that takes CodeChunk
                if not hasattr(self.spec, 'verify') or not self.spec.verify(chunk):
                    logger.warning(f"FormalSpecification does not have verify or verification failed for chunk {idx}.") # FIX: Use module-level logger
                    # Decide how to proceed if verification fails or method is missing
                    if hasattr(self.spec, 'verify'):
                        self.telemetry.track("verification_failure", tags={"chunk_id": str(chunk.id)})
                        raise InvalidCodeHashError(f"Chunk {idx} failed verification")
                    # If verify is missing, maybe just log and continue?
                    # raise InvalidCodeHashError(f"FormalSpecification missing verify method for chunk {idx}")

                # Pass the EnhancedLLMOrchestrator instance's _process_chunk method
                # This ensures the recursive summarizer uses the enhanced processing logic
                summary = self._process_chunk(chunk, allocation[idx])

                # Assuming chunk has an 'id' attribute
                chunk_id_str = str(getattr(chunk, 'id', f'chunk_{idx}')) # Use getattr for safety
                chunk_node_id = self.kg.add_node(Node(type="code_chunk", content=chunk.content, metadata={"chunk_id": chunk_id_str}))

                summary_node = Node(
                    type="code_summary", content=summary, metadata={"source_chunk_id": str(chunk_node_id)}
                )
                summary_node_id = self.kg.add_node(summary_node)
                self.kg.add_edge(chunk_node_id, summary_node_id, "has_summary")
                summaries.append(summary)

        # Assuming summarizer has a synthesize method
        if not hasattr(self.summarizer, 'synthesize'):
             logger.error("RecursiveSummarizer missing synthesize method.") # FIX: Use module-level logger
             raise CriticalFailure("Summarization synthesis method missing.")

        return self.summarizer.synthesize(summaries)


    def _get_model_costs(self):
        # Removed 'mistral-large' to prevent attempting to use an unsupported model
        # Removed 'gpt-4' as it's not handled by _call_llm_api
        # Use the actual configured HF model name for the key
        hf_model_key = self.config.hugging_face_model if self.config.hugging_face_model else "huggingface"
        return {
            "gemini": {"effective_length": 500000, "cost_per_token": 0.000001}, # <-- Increase effective_length here
            hf_model_key: {"effective_length": 4096, "cost_per_token": 0.000002},
        }

    def _process_chunk(self, chunk: CodeChunk, allocation: tuple) -> str:
        tokens, model = allocation
        last_exception = None
        for strategy in self.fallback_strategy:
            with self.telemetry.span(f"strategy_{strategy.__name__}"):
                try:
                    # Pass 'self' (the Enhanced instance) to strategies if they need access
                    # to other EnhancedOrchestrator methods (like _call_llm_api)
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
                    logging.warning(f"Fallback strategy {strategy.__name__} failed: {e}") # This one was already using logging directly

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
        # Call the _call_llm_api method of *this* Enhanced instance
        return self._call_llm_api(optimized, model)

    def _secondary_model(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        if tokens < 500:
            raise ModelCapacityError("Insufficient tokens for secondary model")
        reduced_tokens = int(tokens * 0.75)
        optimized = self.optimizer.optimize(chunk.content, reduced_tokens)
        # Call the _call_llm_api method of *this* Enhanced instance
        return self._call_llm_api(optimized, model)

    def _third_model(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        optimized = self.optimizer.aggressive_optimize(chunk.content, int(tokens * 0.5))
        # Call the _call_llm_api method of *this* Enhanced instance
        return self._call_llm_api(optimized, model)

    def _recursive_summarization_strategy(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        if tokens < 1000:
            raise ModelCapacityError("Insufficient tokens for summarization")
        # The RecursiveSummarizer was initialized with 'self' (the Enhanced instance)
        # so its internal calls to generate/summarize will use the Enhanced logic.
        return self.summarizer.summarize_code_recursively(chunk.content)

    # --- Override _call_llm_api in EnhancedLLMOrchestrator ---
    def _call_llm_api(self, text: str, model: str) -> str:
        """Call the appropriate LLM API, adding telemetry and potentially other logic."""
        # Call the base class's implementation to handle the actual dispatch
        return super()._call_llm_api(text, model)
    # --- END Override ---
# Keep base class _count_tokens if not overridden
def _count_tokens(self, text: str) -> int:
    return len(text.split())
def format_math_prompt(question: str) -> str:
    return f"""Please reason step by step and put your final answer within \\boxed{{}}.

Question: {question}
Answer: """

def extract_boxed_answer(text: str) -> str:
    match = re.search(r"\\boxed{([^}]+)}", text) # FIX: Escape backslash for regex
    if match:
        return match.group(1)