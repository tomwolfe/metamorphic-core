# tests/test_workflow_driver_prompt_construction.py

import pytest
import html
from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT
import logging
from unittest.mock import MagicMock, patch, ANY
import re
from pathlib import Path

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_llm_interaction(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation as they are not needed for LLM interaction tests
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'):
        driver = WorkflowDriver(context)
        # Replace the real orchestrator with a mock
        driver.llm_orchestrator = MagicMock()
        # Default mock return for generate, can be overridden in tests
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        yield driver


class TestWorkflowLlmInteraction:

    # --- Tests for _invoke_coder_llm ---
    def test_invoke_coder_llm_success(self, test_driver_llm_interaction):
        """Test _invoke_coder_llm calls generate and returns stripped response."""
        driver = test_driver_llm_interaction
        test_prompt = "Test prompt for LLM"
        # Simulate LLM returning code with markdown fences
        driver.llm_orchestrator.generate.return_value = "  ```python\nGenerated code response\n```  \n"

        response = driver._invoke_coder_llm(test_prompt)

        driver.llm_orchestrator.generate.assert_called_once_with(test_prompt)
        assert response == "Generated code response"

    def test_invoke_coder_llm_empty_response(self, test_driver_llm_interaction):
        """Test _invoke_coder_llm handles empty response from LLM."""
        driver = test_driver_llm_interaction
        test_prompt = "Test prompt for empty response"
        driver.llm_orchestrator.generate.return_value = ""

        response = driver._invoke_coder_llm(test_prompt)

        driver.llm_orchestrator.generate.assert_called_once_with(test_prompt)
        assert response == ""

    def test_invoke_coder_llm_none_response(self, test_driver_llm_interaction):
        """Test _invoke_coder_llm handles None response from LLM."""
        driver = test_driver_llm_interaction
        test_prompt = "Test prompt for None response"
        driver.llm_orchestrator.generate.return_value = None

        response = driver._invoke_coder_llm(test_prompt)

        driver.llm_orchestrator.generate.assert_called_once_with(test_prompt)
        assert response is None

    def test_invoke_coder_llm_llm_exception(self, test_driver_llm_interaction, caplog):
        """Test _invoke_coder_llm catches exceptions from LLM and returns None."""
        driver = test_driver_llm_interaction
        test_prompt = "Test prompt for exception"
        driver.llm_orchestrator.generate.side_effect = Exception("Test LLM API error")
        caplog.set_level(logging.ERROR)

        response = driver._invoke_coder_llm(test_prompt)

        driver.llm_orchestrator.generate.assert_called_once_with(test_prompt)
        assert response is None
        assert "Error invoking Coder LLM" in caplog.text
        assert "Test LLM API error" in caplog.text

    def test_invoke_coder_llm_strips_different_fences(self, test_driver_llm_interaction):
        """Test _invoke_coder_llm strips different markdown code fences."""
        driver = test_driver_llm_interaction
        test_prompt = "Test prompt"

        # Test with ```
        driver.llm_orchestrator.generate.return_value = "```\nCode 1\n```"
        response1 = driver._invoke_coder_llm(test_prompt)
        assert response1 == "Code 1"

        # Test with ```python
        driver.llm_orchestrator.generate.return_value = "```python\nCode 2\n```"
        response2 = driver._invoke_coder_llm(test_prompt)
        assert response2 == "Code 2"

        # Test with leading/trailing whitespace and fences
        driver.llm_orchestrator.generate.return_value = "  ```python\nCode 3\n```  "
        response3 = driver._invoke_coder_llm(test_prompt)
        assert response3 == "Code 3"

        # Test with only fences
        driver.llm_orchestrator.generate.return_value = "```python\n```"
        response4 = driver._invoke_coder_llm(test_prompt)
        assert response4 == ""

        # Test with fences and only whitespace inside
        driver.llm_orchestrator.generate.return_value = "```python\n  \n```"
        response5 = driver._invoke_coder_llm(test_prompt)
        assert response5 == ""

    # --- Tests for _merge_snippet ---
    def test__merge_snippet_marker_found(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "line1\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        snippet = "inserted_line_a\ninserted_line_b"
        expected = "line1\nline2\ninserted_line_a\ninserted_line_b\nline3"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_marker_not_found(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "line1\nline2\nline3"
        snippet = "inserted_line"
        expected = "line1\nline2\nline3\ninserted_line" # Appends with newline
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_empty_snippet(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "line1\nline2"
        snippet = ""
        merged = driver._merge_snippet(existing, snippet)
        assert merged == existing

    def test__merge_snippet_empty_existing(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = ""
        snippet = "snippet"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == snippet

    def test__merge_snippet_existing_no_newline(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "line1"
        snippet = "snippet"
        expected = "line1\nsnippet" # Appends with newline
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_existing_ends_newline(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "line1\n"
        snippet = "snippet"
        expected = "line1\nsnippet" # Appends directly
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_marker_at_start(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "# METAMORPHIC_INSERT_POINT\nline1"
        snippet = "inserted"
        expected = "inserted\nline1"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_marker_at_end(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "line1\n# METAMORPHIC_INSERT_POINT"
        snippet = "inserted"
        expected = "line1\ninserted"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_multiple_markers(self, test_driver_llm_interaction):
        driver = test_driver_llm_interaction
        existing = "line1\n# METAMORPHIC_INSERT_POINT\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        snippet = "inserted"
        # Should only replace the first marker
        expected = "line1\ninserted\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        merged = driver._merge_snippet(existing, snippet)