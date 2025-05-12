# src/core/chunking/recursive_summarizer.py
import logging
from typing import List, TYPE_CHECKING
# Ensure CodeChunk and MaxSummaryRetriesError are correctly imported or defined
# Assuming CodeChunk is in src.core.chunking and MaxSummaryRetriesError in src.core.exceptions
from src.core.chunking import CodeChunk
from src.core.exceptions import MaxSummaryRetriesError # Make sure this is defined
from src.core.verification import FormalVerificationError, FormalSpecification
from src.core.monitoring import Telemetry

if TYPE_CHECKING:
    from src.core.llm_orchestration import EnhancedLLMOrchestrator

logger = logging.getLogger(__name__)

class RecursiveSummarizer:
    def __init__(self, llm_orchestrator: 'EnhancedLLMOrchestrator', formal_verifier: FormalSpecification, telemetry: Telemetry):
        self.llm = llm_orchestrator
        self.verifier: FormalSpecification = formal_verifier
        self.telemetry = telemetry

    def summarize_code_recursively(self, code: str, depth: int = 3, window_size: int = 3) -> str:
        """
        Recursively summarizes code in 3 passes with a sliding window, ensuring formal verification at each step.
        """
        if depth <= 0:
            return code

        chunks = self._chunk_code(code, window_size)
        summaries = []

        for chunk in chunks:
            with self.telemetry.span("summarization_pass"):
                if not self.verifier.validate_chunks([chunk]):
                    self.telemetry.track('constraint_violation', constraint='ChunkPreSummarizationValidation')
                    logger.warning(f"Chunk failed pre-summarization validation: {chunk.content[:50]}...")
                    raise FormalVerificationError("Chunk failed pre-summarization validation")

                summary = self._generate_summary(chunk.content)

                if not self.verifier.verify(CodeChunk(content=summary)):
                    self.telemetry.track('constraint_violation', constraint='SummaryPostGenerationVerification')
                    logger.warning(f"Summary failed post-generation verification, retrying for chunk: {chunk.content[:50]}...")
                    summary = self._generate_verified_summary(chunk.content)

                summaries.append(summary)

        combined_summary = "\n".join(summaries)
        if depth > 1:
            return self.summarize_code_recursively(combined_summary, depth=depth - 1, window_size=window_size)
        return combined_summary

    def _chunk_code(self, code: str, window_size: int) -> List[CodeChunk]:
        lines = code.splitlines()
        chunks = []
        for i in range(0, len(lines), window_size):
            window = lines[i:i + window_size]
            chunk_content = "\n".join(window)
            chunks.append(CodeChunk(content=chunk_content, estimated_tokens=self.llm._count_tokens(chunk_content)))
        return chunks

    def _generate_summary(self, chunk_content: str, retry=False) -> str:
        prompt = f"Summarize the following code chunk:\n```python\n{chunk_content}\n```\nConcise summary:"
        try:
            return self.llm.generate(prompt)
        except Exception as e:
            if retry:
                logger.error(f"Summarization failed on retry: {e}")
                raise
            logger.warning(f"Initial summarization failed, retrying once: {e}")
            return self._generate_summary(chunk_content, retry=True)

    def _generate_verified_summary(self, chunk_content: str, max_attempts=3, attempt_count=0) -> str:
        if attempt_count >= max_attempts:
            logger.error(f"Max attempts reached for verified summary generation after {max_attempts} retries.")
            raise MaxSummaryRetriesError("Max retries for verified summary generation reached.")

        summary = self._generate_summary(chunk_content)
        if self.verifier.verify(CodeChunk(content=summary)):
            return summary
        else:
            logger.warning(f"Generated summary failed verification, retrying attempt {attempt_count + 1}/{max_attempts}...")
            return self._generate_verified_summary(chunk_content, max_attempts, attempt_count + 1)

    def _is_summary_valid(self, summary: str, original_chunk: CodeChunk) -> bool:
        if not summary.strip():
            return False
        if "summarize" in summary.lower() or "code chunk" in summary.lower():
            return False
        return True

    def _enforce_token_reduction(self, summary: str, original_chunk: CodeChunk) -> str:
        original_tokens = self.llm._count_tokens(original_chunk.content)
        summary_tokens = self.llm._count_tokens(summary)
        if summary_tokens > original_tokens * 0.8:
            logger.warning("Summary exceeds token reduction target, further optimizing.")
            return summary[:int(len(summary) * 0.8)]
        return summary

    # --- BEGIN ADDED METHOD ---
    def synthesize(self, summaries: List[str]) -> str:
        """
        Combines a list of summaries (or processed chunk outputs) into a single string.
        This method is called by EnhancedLLMOrchestrator._handle_large_context.
        """
        logger.info(f"Synthesizing {len(summaries)} summaries into a single output.")
        # Simple concatenation for now. More sophisticated synthesis can be added later if needed.
        return "\n".join(summaries)
    # --- END ADDED METHOD ---