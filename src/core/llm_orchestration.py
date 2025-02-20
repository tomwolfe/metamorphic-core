# src/core/llm_orchestration.py
# llm_orchestration.py
import os
import re
import logging
from enum import Enum
from typing import Optional, List # Import List for type hinting
import google.genai as genai
from huggingface_hub import InferenceClient
from src.utils.config import SecureConfig, ConfigError
from pydantic import BaseModel, ValidationError
from src.core.context_manager import parse_code_chunks  # Import the chunking function
# from src.core.context_manager import CodeChunk # DO NOT IMPORT CodeChunk HERE
from src.core.monitoring import Telemetry
from src.core.verification import FormalVerifier, FormalVerificationError, InvalidCodeHashError, ModelCapacityError, CriticalFailure # Import exceptions
from collections import defaultdict # Import defaultdict
from src.core.chunking.recursive_summarizer import RecursiveSummarizer # Import RecursiveSummarizer
from src.core.chunking.dynamic_chunker import SemanticChunker, CodeChunk # Import CodeChunk
from src.core.optimization.adaptive_token_allocator import TokenAllocator
from src.core.knowledge_graph import KnowledgeGraph, Node # Import KnowledgeGraph for KG interaction
from src.core.optimization.token_optimizer import TokenOptimizer # Import TokenOptimizer
from src.core.verification.specification import FormalSpecification # Import FormalSpecification
from src.core.ethics.governance import EthicalGovernanceEngine # Import EthicalGovernanceEngine

class LLMProvider(str, Enum):
    GEMINI = "gemini"
    HUGGING_FACE = "huggingface"

class LLMConfig(BaseModel):
    provider: LLMProvider
    gemini_api_key: Optional[str] = None
    hf_api_key: Optional[str] = None
    max_retries: int = 3
    timeout: int = 30

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
                provider=LLMProvider(SecureConfig.get('LLM_PROVIDER', 'gemini')),
                gemini_api_key=SecureConfig.get('GEMINI_API_KEY'),
                hf_api_key=SecureConfig.get('HUGGING_FACE_API_KEY'),
                max_retries=int(SecureConfig.get('LLM_MAX_RETRIES', 3)),
                timeout=int(SecureConfig.get('LLM_TIMEOUT', 30))
            )
        except (ValidationError, ConfigError, ValueError) as e:
            logging.error(f"Error loading LLM configuration: {str(e)}")
            raise RuntimeError(f"Invalid LLM configuration: {str(e)}")

    def _configure_providers(self):
        if self.config.provider == LLMProvider.GEMINI:
            if not self.config.gemini_api_key:
                raise RuntimeError("GEMINI_API_KEY is required for Gemini provider")
            self.client = genai.Client(api_key=self.config.gemini_api_key)
            self.client.model = 'gemini-2.0-flash-exp'
            self.client.api_key = self.config.gemini_api_key
        elif self.config.provider == LLMProvider.HUGGING_FACE:
            if not self.config.hf_api_key:
                raise RuntimeError("HUGGING_FACE_API_KEY is required for Hugging Face provider")
            self.client = InferenceClient(
                token=self.config.hf_api_key,
                model="deepseek-ai/DeepSeek-R1-Distill-Qwen-32B"
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
                return self._hf_generate(prompt)
            except Exception as e:
                logging.error(f"Attempt {attempt + 1} failed: {str(e)}")
                if attempt == self.config.max_retries - 1:
                    raise RuntimeError(f"LLM API failed after {self.config.max_retries} attempts: {str(e)}")

    def _gemini_generate(self, prompt: str) -> str:
        try:
            response = self.client.models.generate_content(
                model=self.client.model,
                contents=prompt,
                config=genai.types.GenerateContentConfig(temperature=0.6, top_p=0.95)
            )
            return ''.join(part.text for part in response.candidates[0].content.parts)
        except Exception as e:
            logging.error(f"Gemini error: {str(e)}")
            raise RuntimeError(f"Gemini error: {str(e)}")

    def _hf_generate(self, prompt: str) -> str:
        try:
            return self.client.text_generation(
                prompt,
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
    def __init__(self, kg: KnowledgeGraph, spec: FormalSpecification, ethics_engine: EthicalGovernanceEngine): # Add spec and ethics_engine
        super().__init__()
        self.verifier = FormalVerifier()
        self.telemetry = Telemetry()
        self.chunker = SemanticChunker()  # Instantiate SemanticChunker
        self.allocator = TokenAllocator(total_budget=50000) # Example budget
        self.optimizer = TokenOptimizer() # Instantiate TokenOptimizer
        self.summarizer = RecursiveSummarizer(self, self.verifier, self.telemetry) # Instantiate RecursiveSummarizer, pass telemetry
        self.kg = kg # Store KnowledgeGraph instance
        self.spec = spec # Store FormalSpecification
        self.ethics_engine = ethics_engine # Store EthicalGovernanceEngine
        self.fallback_strategy = [
            self._primary_processing,
            self._secondary_model,
            self._third_model, # Add third model
            self._recursive_summarization_strategy # Use recursive summarization strategy
        ]

    def generate(self, prompt: str) -> str:
        self.telemetry.start_session()
        try:
            if self._count_tokens(prompt) > 4000:
                return self._handle_large_context(prompt)
            return super().generate(prompt)
        except FormalVerificationError as e: # Catch verification errors
            self.telemetry.track('error', type='FormalVerificationError', message=str(e)) # Telemetry error track
            raise # Re-raise after telemetry log
        except Exception as e: # Catch any other exceptions
            self.telemetry.track('error', type='GenericError', message=str(e)) # Generic error track
            raise # Re-raise
        finally:
            self.telemetry.publish()

    def _handle_large_context(self, prompt: str) -> str:
        chunks = self.chunker.chunk(prompt)
        if not self.verifier.validate_chunks(chunks): # Use FormalVerifier for chunk validation
            self.telemetry.track('constraint_violation', constraint='InitialChunkValidation') # Telemetry - initial validation fail
            raise FormalVerificationError("Initial chunk validation failed") # Raise verification error

        allocation = self.allocator.allocate(chunks, self._get_model_costs()) # Pass model costs
        summaries = []

        for idx, chunk in enumerate(chunks):
            with self.telemetry.span(f"chunk_{idx}"):
                if not self.verifier.verify(chunk): # Pass CodeChunk object for Coq verification
                    self.telemetry.track('verification_failure', chunk_id=str(chunk.id)) # Telemetry - verification fail
                    raise InvalidCodeHashError(f"Chunk {idx} failed Coq verification") # Raise specific verification error
                summary = self._process_chunk(chunk, allocation[idx])
                chunk_node_id = self.kg.add_node(chunk) # Store chunk in KG and get ID
                summary_node = Node(type="code_summary", content=summary, metadata={"source_chunk_id": str(chunk_node_id)}) # Create summary node
                summary_node_id = self.kg.add_node(summary_node) # Add summary node to KG
                self.kg.add_edge(chunk_node_id, summary_node_id, "has_summary") # Link in KG
                summaries.append(summary)

        return self.synthesizer.synthesize(summaries)

    def _get_model_costs(self):
        """Return current model cost and length constraints (simulated)."""
        # In real system, these could be dynamically fetched or configured
        return {
            'gemini': {'effective_length': 8000, 'cost_per_token': 1},
            'gpt-4': {'effective_length': 32000, 'cost_per_token': 10},
            'mistral-large': {'effective_length': 32000, 'cost_per_token': 5} # Example third model
        }

    def _process_chunk(self, chunk: CodeChunk, allocation: tuple) -> str:
        tokens, model = allocation
        for strategy in self.fallback_strategy:
            with self.telemetry.span(f"strategy_{strategy.__name__}"): # Track each strategy
                try:
                    result = strategy(chunk, tokens, model)
                    self.telemetry.track('model_success', model=model, strategy=strategy.__name__) # Track success
                    return result
                except OrchestrationError as e:
                    self.telemetry.track('model_fallback', model=model, strategy=strategy.__name__, error=str(e)) # Track fallback
        raise CriticalFailure("All processing strategies failed")

    @formal_proof("""
    Lemma fallback_termination:
      forall chunk, exists n, strategy_n(chunk) terminates
    """)
    def _primary_processing(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        optimized = self.optimizer.optimize(chunk.content, tokens)
        return self._call_llm_api(optimized, model)

    def _secondary_model(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        """Use secondary LLM with reduced token budget if primary fails"""
        if tokens < 500: raise ModelCapacityError("Insufficient tokens for secondary model")
        reduced_tokens = int(tokens * 0.75) # Reduce tokens by 25%
        optimized = self.optimizer.optimize(chunk.content, reduced_tokens)
        return self._call_llm_api(optimized, model)

    def _third_model(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        """Use third LLM with aggressive optimization if secondary also fails"""
        optimized = self.optimizer.aggressive_optimize(chunk.content, int(tokens * 0.5)) # Reduce tokens by 50%
        return self._call_llm_api(optimized, model)

    def _recursive_summarization_strategy(self, chunk: CodeChunk, tokens: int, model: str) -> str:
        """Apply recursive summarization if other strategies fail."""
        if tokens < 1000: raise ModelCapacityError("Insufficient tokens for summarization")
        return self.summarizer.summarize_code_recursively(chunk.content) # Use RecursiveSummarizer

    def _count_tokens(self, text: str) -> int:
        """Token counting (placeholder - replace with actual tokenizer)."""
        return len(text.split()) # Simple word count as token estimate

def format_math_prompt(question: str) -> str:
    return f"""Please reason step by step and put your final answer within \\boxed{{}}.

Question: {question}
Answer: """

def extract_boxed_answer(text: str) -> str:
    match = re.search(r'\\boxed{([^}]+)}', text)
    if match:
        return match.group(1)
