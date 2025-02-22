# src/core/chunking/recursive_summarizer.py
import logging
from typing import List, TYPE_CHECKING
from src.core.chunking import CodeChunk
from src.core.verification import FormalVerificationError # Import FormalVerificationError
from src.core.verification import FormalSpecification
from src.core.monitoring import Telemetry # Import Telemetry

if TYPE_CHECKING:
    from src.core.llm_orchestration import EnhancedLLMOrchestrator

logger = logging.getLogger(__name__)

class RecursiveSummarizer:
    def __init__(self, llm_orchestrator: 'EnhancedLLMOrchestrator', formal_verifier: FormalSpecification, telemetry: Telemetry): # Add Telemetry
        self.llm = llm_orchestrator
        self.verifier: FormalSpecification = formal_verifier
        self.telemetry = telemetry # Store Telemetry

    def summarize_code_recursively(self, code: str, depth: int = 3, window_size: int = 3) -> str:
        """
        Recursively summarizes code in 3 passes with a sliding window, ensuring formal verification at each step.
        """
        if depth <= 0:
            return code  # Base case: no more summarization needed

        chunks = self._chunk_code(code, window_size)
        summaries = []

        for chunk in chunks:
            with self.telemetry.span("summarization_pass"):
                # Verify chunk BEFORE summarization attempt
                if not self.verifier.validate_chunks([chunk]): # Pass chunk list
                    self.telemetry.track('constraint_violation', constraint='ChunkPreSummarizationValidation') # Telemetry
                    logger.warning(f"Chunk failed pre-summarization validation: {chunk.content[:50]}...")
                    raise FormalVerificationError("Chunk failed pre-summarization validation") # Raise exception

                summary = self._generate_summary(chunk.content)

                # Verify summary AFTER generation
                if not self.verifier.verify(CodeChunk(content=summary)): # Verify summary as CodeChunk
                    self.telemetry.track('constraint_violation', constraint='SummaryPostGenerationVerification') # Telemetry
                    logger.warning(f"Summary failed post-generation verification, retrying for chunk: {chunk.content[:50]}...")
                    summary = self._generate_verified_summary(chunk.content) # Retry with verification

                summaries.append(summary)

        combined_summary = "\n".join(summaries)
        if depth > 1:
            return self.summarize_code_recursively(combined_summary, depth=depth - 1, window_size=window_size) # Recursive call
        return combined_summary

    def _chunk_code(self, code: str, window_size: int) -> List[CodeChunk]:
        """Sliding window chunking (simple example, can be enhanced)."""
        lines = code.splitlines()
        chunks = []
        for i in range(0, len(lines), window_size):
            window = lines[i:i + window_size]
            chunk_content = "\n".join(window)
            chunks.append(CodeChunk(content=chunk_content, estimated_tokens=self.llm._count_tokens(chunk_content))) # Estimate tokens
        return chunks

    def _generate_summary(self, chunk_content: str, retry=False) -> str:
        """Generates summary for a code chunk using LLM, with retry mechanism."""
        prompt = f"Summarize the following code chunk:\n```python\n{chunk_content}\n```\nConcise summary:"
        try:
            return self.llm.generate(prompt)  # Use EnhancedLLMOrchestrator's generate method
        except Exception as e:
            if retry:
                logger.error(f"Summarization failed on retry: {e}")
                raise  # Re-raise exception after retry attempt fails
            logger.warning(f"Initial summarization failed, retrying once: {e}")
            return self._generate_summary(chunk_content, retry=True)  # Recursive retry call

    def _generate_verified_summary(self, chunk_content: str, max_attempts=3, attempt_count=0) -> str: # Verified summary generation
        """Attempts to generate a verified summary, with retries and fallback."""
        if attempt_count >= max_attempts:
            logger.error(f"Max attempts reached for verified summary generation after {max_attempts} retries.")
            raise MaxSummaryRetriesError("Max retries for verified summary generation reached.")

        summary = self._generate_summary(chunk_content)
        if self.verifier.verify(CodeChunk(content=summary)): # Verify generated summary
            return summary
        else:
            logger.warning(f"Generated summary failed verification, retrying attempt {attempt_count + 1}/{max_attempts}...")
            return self._generate_verified_summary(chunk_content, max_attempts, attempt_count + 1) # Recursive retry

    def _is_summary_valid(self, summary: str, original_chunk: CodeChunk) -> bool:
        """Placeholder for formal summary validation (e.g., semantic similarity, keyword retention)."""
        # In a real system, this would involve more sophisticated checks, possibly using Z3 or Coq
        if not summary.strip():
            return False  # Reject empty summaries
        if "summarize" in summary.lower() or "code chunk" in summary.lower():
            return False  # Reject generic/placeholder summaries
        return True  # Basic placeholder validation - replace with formal verification

    def _enforce_token_reduction(self, summary: str, original_chunk: CodeChunk) -> str:
        """Placeholder for enforcing token reduction in summaries."""
        # In a real system, you might have more advanced token counting and reduction strategies
        original_tokens = self.llm._count_tokens(original_chunk.content) # Assuming token counting in orchestrator
        summary_tokens = self.llm._count_tokens(summary)
        if summary_tokens > original_tokens * 0.8:  # Example: enforce 20% reduction
            logger.warning("Summary exceeds token reduction target, further optimizing.")
            # Placeholder for more aggressive summarization or token trimming
            return summary[:int(len(summary) * 0.8)] # Aggressively trim summary - replace with better method
        return summary
