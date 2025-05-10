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
from src.core.chunking.recursive_summarizer import RecursiveSummarizer
from src.core.chunking.dynamic_chunker import SemanticChunker, CodeChunk
from src.core.optimization.adaptive_token_allocator import TokenAllocator
from src.core.knowledge_graph import KnowledgeGraph, Node
from src.core.optimization.token_optimizer import TokenOptimizer
from src.core.verification.specification import FormalSpecification
from src.core.verification.decorators import formal_proof

if TYPE_CHECKING:
    from src.core.ethics.governance import EthicalGovernanceEngine


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
    def __init__(self):
        self.client = None
        self.active_provider = None
        self.config = self._load_config()
        self._configure_providers()

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
            logging.error(f"Error loading LLM configuration: {str(e)}")
            raise RuntimeError(f"Invalid LLM configuration: {str(e)}")

    def _configure_providers(self):
        if self.config.provider == LLMProvider.GEMINI:
            if not self.config.gemini_api_key:
                raise RuntimeError("GEMINI_API_KEY is required for Gemini provider")
            self.client = genai.Client(api_key=self.config.gemini_api_key)
            self.client.model = "gemini-2.5-flash-preview-04-17" # <-- UPDATED HERE
            self.client.api_key = self.config.gemini_api_key
        elif self.config.provider == LLMProvider.HUGGING_FACE:
            if not self.config.hf_api_key:
                raise RuntimeError("HUGGING_FACE_API_KEY is required for Hugging Face provider")
            self.client = InferenceClient(
                token=self.config.hf_api_key,
                model=self.config.hugging_face_model,
            )
        else:
            raise ValueError(f"Unsupported LLM provider: {self.config.provider}")

    def generate(self, prompt: str) -> str:
        return self._generate_with_retry(prompt)

    def _generate_with_retry(self, prompt: str) -> str:
        for attempt in range(self.config.max_retries):
            try:
                if self.config.provider == LLMProvider.GEMINI:
                    return self._gemini_generate(prompt)
                elif self.config.provider == LLMProvider.HUGGING_FACE:
                    return self._hf_generate(prompt)
            except Exception as e:
                logging.error(f"Attempt {attempt + 1} failed: {str(e)}")
                if attempt == self.config.max_retries - 1:
                    raise RuntimeError(f"LLM API failed after {self.config.max_retries} attempts: {str(e)}")

    def _gemini_generate(self, prompt: str) -> str:
        try:
            response = self.client.models.generate_content(
                model="gemini-2.5-flash-preview-04-17", # <-- UPDATED HERE
                contents=prompt,
                config=genai.types.GenerateContentConfig(
                    temperature=0.6,
                    top_p=0.95,
                ),
            )
            if response.candidates and response.candidates[0].content and response.candidates[0].content.parts:
                parts = response.candidates[0].content.parts
                return "".join(part.text for part in parts if hasattr(part, "text"))
            return ""
        except Exception as e:
            logging.error(f"Gemini error: {str(e)}")
            raise RuntimeError(f"Gemini error: {str(e)}")

    def _hf_generate(self, prompt: str) -> str:
        try:
            return self.client.text_generation(
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
            logging.error(f"Hugging Face error: {str(e)}")
            raise RuntimeError(f"Hugging Face error: {str(e)}")

class EnhancedLLMOrchestrator(LLMOrchestrator):
    # rest of the EnhancedLLMOrchestrator class remains the same.
    def __init__(
            self, kg: KnowledgeGraph, spec: FormalSpecification, ethics_engine: "EthicalGovernanceEngine"
    ):
        super().__init__()
        self.telemetry = Telemetry()
        self.chunker = SemanticChunker()
        self.allocator = TokenAllocator(total_budget=50000)
        self.optimizer = TokenOptimizer()
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

    def generate(self, prompt: str) -> str:
        self.telemetry.start_session()
        try:
            with self.telemetry.span("generate_logic"):
                if self._count_tokens(prompt) > 4000:
                    code = self._handle_large_context(prompt)
                else:
                    model = self.config.provider.value
                    self.telemetry.track("model_usage", tags={"model": model})
                    code = super().generate(prompt)

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
        if not self.spec.validate_chunks(chunks):
            self.telemetry.track("constraint_violation", tags={"constraint": "InitialChunkValidation"})
            raise FormalVerificationError("Initial chunk validation failed")

        allocation = self.allocator.allocate(chunks, self._get_model_costs())
        summaries = []

        for idx, chunk in enumerate(chunks):
            with self.telemetry.span(f"chunk_{idx}"):
                if not self.spec.verify(chunk):
                    self.telemetry.track("verification_failure", tags={"chunk_id": str(chunk.id)})
                    raise InvalidCodeHashError(f"Chunk {idx} failed Coq verification")
                summary = self._process_chunk(chunk, allocation[idx])
                chunk_node_id = self.kg.add_node(chunk)
                summary_node = Node(
                    type="code_summary", content=summary, metadata={"source_chunk_id": str(chunk_node_id)}
                )
                summary_node_id = self.kg.add_node(summary_node)
                self.kg.add_edge(chunk_node_id, summary_node_id, "has_summary")
                summaries.append(summary)

        return self.summarizer.synthesize(summaries)

    def _get_model_costs(self):
        # --- MODIFICATION START ---
        # Removed 'mistral-large' to prevent attempting to use an unsupported model
        return {
            "gemini": {"effective_length": 8000, "cost_per_token": 0.000001},
            "gpt-4": {"effective_length": 8000, "cost_per_token": 0.00003},
            # "mistral-large": {"effective_length": 32000, "cost_per_token": 0.000002}, # Removed
        }
        # --- MODIFICATION END ---

    def _process_chunk(self, chunk: CodeChunk, allocation: tuple) -> str:
        tokens, model = allocation
        last_exception = None
        for strategy in self.fallback_strategy:
            with self.telemetry.span(f"strategy_{strategy.__name__}"):
                try:
                    result = strategy(chunk, tokens, model)
                    self.telemetry.track("model_success", tags={"model": model, "strategy": strategy.__name__})
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
        self.telemetry.track("model_usage", tags={"model": model})
        if model == "gemini":
            return self._gemini_generate(text)
        elif model in ["huggingface", "hf"]:
            return self._hf_generate(text)
        else:
            raise ValueError(f"Unsupported model: {model}")

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