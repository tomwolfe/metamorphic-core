# tests/test_workflow_driver_enhancements.py

import pytest
import re
import json
from pathlib import Path
import logging
from unittest.mock import patch, MagicMock, call, ANY

# Import necessary components from workflow_driver
from src.core.automation.workflow_driver import (
    WorkflowDriver,
    Context,
    METAMORPHIC_INSERT_POINT,
    DOCSTRING_INSTRUCTION_PYTHON,
    PYTHON_CREATION_KEYWORDS,
)

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(name)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with mocked dependencies for isolated testing
@pytest.fixture
def driver_enhancements(tmp_path, mocker):
    context = Context(str(tmp_path))

    # Mock dependencies that WorkflowDriver's __init__ or methods might use
    mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
    mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
    mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
    mocker.patch.object(WorkflowDriver, '_load_default_policy')

    # Mock context.get_full_path for predictable path resolution
    def mock_get_full_path_side_effect(relative_path_str):
        if relative_path_str is None:
            return None
        # Simulate resolution within tmp_path
        return str((tmp_path / relative_path_str).resolve())

    mocker.patch.object(context, 'get_full_path', side_effect=mock_get_full_path_side_effect)

    driver = WorkflowDriver(context)
    driver.llm_orchestrator = MagicMock() # Ensure LLM orchestrator is a mock
    driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure policy is loaded

    # Mock internal methods that are called during prompt construction but not directly tested here
    # These mocks will be controlled per test case to simulate different conditions
    mocker.patch.object(driver, '_is_add_imports_step', return_value=False)
    mocker.patch.object(driver, '_find_import_block_end', return_value=0)
    mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)

    yield driver

class TestWorkflowDriverPromptRefinement:
    """
    Tests for the CoderLLM prompt refinement logic, assuming _construct_coder_llm_prompt
    method exists in WorkflowDriver.
    """

    @pytest.mark.parametrize("step_description, expected_instruction_substring", [
        ("Implement a new function.", "1. Ensure all string literals are correctly terminated"),
        ("Add a class definition.", "2. Pay close attention to Python's indentation rules."),
        ("Refactor the main logic.", "3. Generate complete and runnable Python code snippets."),
        ("Fix a bug in the utility module.", "4. If modifying existing code, ensure the snippet integrates seamlessly"),
    ])
    def test_coder_prompt_includes_general_guidelines(self, driver_enhancements, step_description, expected_instruction_substring):
        """
        Verify that the general snippet generation guidelines are included in the prompt
        when no specific conditions (like imports or docstrings) are met.
        """
        driver = driver_enhancements
        mock_task = {
            'task_id': 'test_task',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'target_file': 'src/test_file.py'
        }
        mock_filepath = 'src/test_file.py'
        mock_existing_content = 'existing code'

        # Ensure internal methods that influence prompt construction are mocked as needed for this test
        driver._is_add_imports_step.return_value = False
        driver._should_add_docstring_instruction.return_value = False

        # Call the SUT's prompt construction method
        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, step_description, mock_filepath, mock_existing_content
        )

        assert expected_instruction_substring in coder_prompt
        # Also assert that import-specific and docstring instructions are NOT present
        assert "You are adding import statements." not in coder_prompt
        assert DOCSTRING_INSTRUCTION_PYTHON not in coder_prompt

    def test_coder_prompt_includes_import_specific_guidelines(self, driver_enhancements):
        """Verify that import-specific guidelines are included when applicable."""
        driver = driver_enhancements
        mock_task = {
            'task_id': 'import_task',
            'task_name': 'Add new imports',
            'description': 'Add imports to src/main.py',
            'target_file': 'src/main.py'
        }
        mock_filepath = 'src/main.py'
        mock_existing_content = 'import os\n\n# METAMORPHIC_INSERT_POINT\n\ndef main(): pass'

        # Configure mocks to simulate an import step
        driver._is_add_imports_step.return_value = True # This is the key mock for this test
        driver._should_add_docstring_instruction.return_value = False # Ensure docstring is off

        # Call the SUT's prompt construction method
        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, mock_task['description'], mock_filepath, mock_existing_content
        )

        assert "You are adding import statements." in coder_prompt
        assert "Do not repeat existing imports." in coder_prompt
        # Also verify general guidelines are still present (as they are appended)
        assert "1. Ensure all string literals are correctly terminated" in coder_prompt
        assert DOCSTRING_INSTRUCTION_PYTHON not in coder_prompt


    def test_coder_prompt_includes_docstring_instruction_when_needed(self, driver_enhancements):
        """Verify that the docstring instruction is added when _should_add_docstring_instruction returns True."""
        driver = driver_enhancements
        mock_task = {
            'task_id': 'docstring_task',
            'task_name': 'Create new function',
            'description': 'Implement a new Python function.',
            'target_file': 'src/new_module.py'
        }
        mock_filepath = 'src/new_module.py'
        mock_existing_content = ''

        # Configure mocks to simulate a new function creation step
        driver._is_add_imports_step.return_value = False # Ensure not an import step
        driver._should_add_docstring_instruction.return_value = True # This is the key mock for this test

        # Call the SUT's prompt construction method
        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, mock_task['description'], mock_filepath, mock_existing_content
        )

        assert DOCSTRING_INSTRUCTION_PYTHON in coder_prompt
        # Verify general guidelines are also present
        assert "1. Ensure all string literals are correctly terminated" in coder_prompt
        assert "You are adding import statements." not in coder_prompt

class TestWorkflowDriverMergeStrategy:
    """Tests for the improved _merge_snippet method."""

    @pytest.mark.parametrize("existing_content, snippet, expected_merged_content", [
        # Marker found, no indentation
        ("line1\n# METAMORPHIC_INSERT_POINT\nline3", "inserted_line", "line1\ninserted_line\nline3"),
        # Marker found, with indentation
        ("    line1\n    # METAMORPHIC_INSERT_POINT\n    line3", "inserted_line", "    line1\n    inserted_line\n    line3"),
        # Marker found, multi-line snippet, with indentation
        ("    line1\n    # METAMORPHIC_INSERT_POINT\n    line3", "line_a\nline_b", "    line1\n    line_a\n    line_b\n    line3"),
        # Marker found, empty snippet
        ("line1\n# METAMORPHIC_INSERT_POINT\nline3", "", "line1\n\nline3"), # Empty snippet should replace marker with just its indentation
        # Marker at start of file
        ("# METAMORPHIC_INSERT_POINT\nline1", "inserted", "inserted\nline1"),
        # Marker at end of file
        ("line1\n# METAMORPHIC_INSERT_POINT", "inserted", "line1\ninserted"),
        # No marker, existing ends with newline
        ("line1\nline2\n", "inserted", "line1\nline2\ninserted"),
        # No marker, existing does not end with newline
        ("line1\nline2", "inserted", "line1\nline2\ninserted"),
        # Empty existing content, no marker
        ("", "snippet", "snippet"),
        # Empty existing content, with marker (should still apply indentation if marker implies it)
        ("    # METAMORPHIC_INSERT_POINT", "snippet", "    snippet"),
        # Snippet with internal indentation
        # FIX: Corrected expected_merged_content for this case
        ("    # METAMORPHIC_INSERT_POINT", "def func():\n        pass", "    def func():\n            pass"),
        # Snippet with internal indentation and existing content indentation
        ("class MyClass:\n    # METAMORPHIC_INSERT_POINT\n    def method(): pass", "    def new_method():\n        pass", "class MyClass:\n    def new_method():\n        pass\n    def method(): pass"),
    ])
    def test_merge_snippet_with_indentation_logic(self, driver_enhancements, existing_content, snippet, expected_merged_content):
        """Verify _merge_snippet correctly applies indentation based on the marker's line."""
        driver = driver_enhancements
        merged = driver._merge_snippet(existing_content, snippet)
        assert merged == expected_merged_content

    def test_merge_snippet_no_marker_empty_snippet(self, driver_enhancements):
        """Verify _merge_snippet returns original content if snippet is empty and no marker."""
        driver = driver_enhancements
        existing = "line1\nline2"
        snippet = ""
        merged = driver._merge_snippet(existing, snippet)
        assert merged == existing

    def test_merge_snippet_no_marker_empty_existing(self, driver_enhancements):
        """Verify _merge_snippet returns snippet if existing content is empty and no marker."""
        driver = driver_enhancements
        existing = ""
        snippet = "new_code"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == snippet

    def test_merge_snippet_multiple_markers_only_first_replaced(self, driver_enhancements):
        """Verify _merge_snippet only replaces the first occurrence of the marker."""
        driver = driver_enhancements
        existing = "line1\n# METAMORPHIC_INSERT_POINT\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        snippet = "inserted"
        expected = "line1\ninserted\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected