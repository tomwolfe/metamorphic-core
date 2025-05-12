# In tests/test_recursive_summarizer.py or similar
import pytest
from src.core.chunking.recursive_summarizer import RecursiveSummarizer
from unittest.mock import MagicMock

def test_recursive_summarizer_synthesize():
    mock_llm_orchestrator = MagicMock()
    mock_formal_verifier = MagicMock()
    mock_telemetry = MagicMock()
    summarizer = RecursiveSummarizer(mock_llm_orchestrator, mock_formal_verifier, mock_telemetry)
    
    summaries_list = ["Summary of chunk 1.", "Generated code for chunk 2.", "Final thoughts for chunk 3."]
    expected_synthesis = "Summary of chunk 1.\nGenerated code for chunk 2.\nFinal thoughts for chunk 3."
    
    actual_synthesis = summarizer.synthesize(summaries_list)
    assert actual_synthesis == expected_synthesis

def test_recursive_summarizer_synthesize_empty_list():
    mock_llm_orchestrator = MagicMock()
    mock_formal_verifier = MagicMock()
    mock_telemetry = MagicMock()
    summarizer = RecursiveSummarizer(mock_llm_orchestrator, mock_formal_verifier, mock_telemetry)
    
    actual_synthesis = summarizer.synthesize([])
    assert actual_synthesis == ""
