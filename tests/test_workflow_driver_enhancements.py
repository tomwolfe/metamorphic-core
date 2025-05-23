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
    END_OF_CODE_MARKER, # Import the new constant
    GENERAL_SNIPPET_GUIDELINES, # <--- Ensure this is imported
)

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(name)s - %(message)s')
logger = logging.getLogger(__name__)

# Define the exact expected strings for the output format instructions
# These should match the strings generated in src/core/automation/workflow_driver.py
_EXPECTED_DEFAULT_OUTPUT_FORMAT_INSTRUCTION_PART = f"IMPORTANT: End your code snippet with the exact marker line: `{END_OF_CODE_MARKER}`"
_EXPECTED_IMPORT_SPECIFIC_GUIDANCE_PART = f"IMPORTANT: End your import lines with the exact marker line: `{END_OF_CODE_MARKER}`"

_FULL_DEFAULT_OUTPUT_FORMAT_INSTRUCTION = (
    "Generate only the Python code snippet needed to fulfill the \"Specific Plan Step\". "
    "Do not include any surrounding text, explanations, or markdown code block fences (```). "
    "Provide just the raw code lines that need to be added or modified.\n"
    f"{_EXPECTED_DEFAULT_OUTPUT_FORMAT_INSTRUCTION_PART}\n"
)

_FULL_IMPORT_SPECIFIC_GUIDANCE = (
    "You are adding import statements. Do not repeat existing imports. Do not output any other code or explanation. "
    "Place the new imports appropriately within or after the existing import block.\n"
    f"{_EXPECTED_IMPORT_SPECIFIC_GUIDANCE_PART}\n"
)

# NEW CONSTANTS FOR REFINED PROMPT
_CRITICAL_OUTPUT_INSTRUCTIONS = (
    "CRITICAL INSTRUCTIONS FOR YOUR RESPONSE FORMAT:\n"
    "1. Your entire response MUST be ONLY a valid Python code snippet.\n"
    "2. Do NOT include any explanations, introductory text, apologies, or markdown formatting like ```python or ```.\n"
    "3. The Python code snippet you generate will be directly parsed and inserted into an existing Python file.\n"
    # This constant must exactly match the string produced by the SUT's f-string.
    # The SUT's f-string uses {{...}} for the example, so the test constant should too.
    f"4. Your Python code snippet MUST end with the exact marker line, on its own line, with no preceding or trailing characters on that line: `{END_OF_CODE_MARKER}` (e.g., `# {{METAMORPHIC_END_OF_CODE_SNIPPET}}`)\n"
    "5. If the plan step asks for an explanation or analysis, and you are invoked as a CoderLLM, this is an error. In such a case, output only a Python comment explaining the error and then the marker. Example: `# ERROR: This step requires analysis, not code generation.\\n# {{METAMORPHIC_END_OF_CODE_SNIPPET}}`"
)

_NEW_INTRODUCTORY_LINE_TEMPLATE = "Based on the \"Specific Plan Step\" below, generate the required Python code snippet to modify the target file (`{filepath_to_use}`)."

# This is the full string including the example, as it appears in the prompt
_DOCSTRING_INSTRUCTION_WITH_EXAMPLE = f"{DOCSTRING_INSTRUCTION_PYTHON} # (e.g., 'IMPORTANT: For any new Python functions... you MUST include a comprehensive PEP 257 compliant docstring.')" # No curly braces here, so this line is fine.
# The SUT adds leading/trailing newlines to this block. The test constant should reflect that.
_DOCSTRING_INSTRUCTION_WITH_EXAMPLE_IN_PROMPT = f"\n{DOCSTRING_INSTRUCTION_PYTHON} # (e.g., 'IMPORTANT: For any new Python functions... you MUST include a comprehensive PEP 257 compliant docstring.')\n\n"


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
        ("Implement a new function.", "1. Your entire response MUST be ONLY a valid Python code snippet."),
        ("Add a class definition.", "2. Do NOT include any explanations, introductory text, apologies, or markdown formatting"),
        ("Refactor the main logic.", "3. The Python code snippet you generate will be directly parsed"),
        ("Fix a bug in the utility module.", f"4. Your Python code snippet MUST end with the exact marker line, on its own line, with no preceding or trailing characters on that line: `{END_OF_CODE_MARKER}` (e.g., `# {{METAMORPHIC_END_OF_CODE_SNIPPET}}`)\n"),
        ("Analyze the requirements.", "5. If the plan step asks for an explanation or analysis"), # Test point 5
    ])
    def test_coder_prompt_includes_critical_output_instructions_and_new_intro(self, driver_enhancements, step_description, expected_instruction_substring):
        """
        Verify that the new critical output instructions are at the top of the prompt
        and the new introductory line is present.
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

        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, step_description, mock_filepath, mock_existing_content
        )

        # Assert critical instructions are present
        assert expected_instruction_substring in coder_prompt
        assert _CRITICAL_OUTPUT_INSTRUCTIONS in coder_prompt # Check the whole block

        # Assert new introductory line is present and correctly formatted
        expected_intro_line = _NEW_INTRODUCTORY_LINE_TEMPLATE.format(filepath_to_use=mock_filepath)
        assert expected_intro_line in coder_prompt

        # Assert the order: critical instructions should come before the new intro line
        assert coder_prompt.find(_CRITICAL_OUTPUT_INSTRUCTIONS) < coder_prompt.find(expected_intro_line)

        # Assert other conditional parts are NOT present
        assert _DOCSTRING_INSTRUCTION_WITH_EXAMPLE not in coder_prompt
        assert "SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:" not in coder_prompt
        # Ensure GENERAL_SNIPPET_GUIDELINES are still present at the end
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt

    def test_coder_prompt_includes_docstring_instruction_with_example(self, driver_enhancements):
        """
        Verify that the docstring instruction is added with its example when _should_add_docstring_instruction returns True.
        """
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

        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, mock_task['description'], mock_filepath, mock_existing_content
        )

        # Assert the docstring instruction with example is present
        assert _DOCSTRING_INSTRUCTION_WITH_EXAMPLE_IN_PROMPT in coder_prompt

        # Assert other parts are present as expected
        assert _CRITICAL_OUTPUT_INSTRUCTIONS in coder_prompt
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt
        expected_intro_line = _NEW_INTRODUCTORY_LINE_TEMPLATE.format(filepath_to_use=mock_filepath)
        assert expected_intro_line in coder_prompt

        # Assert conditional parts are NOT present
        assert "SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:" not in coder_prompt

    def test_coder_prompt_includes_import_specific_guidelines_and_new_intro(self, driver_enhancements):
        """
        Verify that import-specific guidelines are included and the new intro line is present.
        """
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

        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, mock_task['description'], mock_filepath, mock_existing_content
        )

        # Assert import-specific guidance is present
        assert "SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:" in coder_prompt
        assert "You are adding import statements." in coder_prompt

        # Assert new introductory line is present
        expected_intro_line = _NEW_INTRODUCTORY_LINE_TEMPLATE.format(filepath_to_use=mock_filepath)
        assert expected_intro_line in coder_prompt

        # Assert other parts are present as expected
        assert _CRITICAL_OUTPUT_INSTRUCTIONS in coder_prompt
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt

        # Assert conditional parts are NOT present
        assert _DOCSTRING_INSTRUCTION_WITH_EXAMPLE not in coder_prompt

    def test_coder_prompt_all_conditional_elements_present(self, driver_enhancements):
        """
        Verify that all conditional elements (docstring, imports) are present when applicable,
        along with critical instructions and new intro.
        """
        driver = driver_enhancements
        mock_task = {
            'task_id': 'complex_task',
            'task_name': 'Add imports and create new function',
            'description': 'Add necessary imports and implement a new utility function in src/utils.py',
            'target_file': 'src/utils.py'
        }
        mock_filepath = 'src/utils.py'
        mock_existing_content = 'existing_code'

        # Configure mocks to trigger both conditional elements
        driver._is_add_imports_step.return_value = True
        driver._should_add_docstring_instruction.return_value = True

        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, mock_task['description'], mock_filepath, mock_existing_content
        )

        # Assert all expected parts are present
        assert _CRITICAL_OUTPUT_INSTRUCTIONS in coder_prompt
        expected_intro_line = _NEW_INTRODUCTORY_LINE_TEMPLATE.format(filepath_to_use=mock_filepath)
        assert expected_intro_line in coder_prompt
        assert _DOCSTRING_INSTRUCTION_WITH_EXAMPLE in coder_prompt
        assert "SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:" in coder_prompt
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt

        # Assert order of conditional elements (docstring instruction comes before import guidance in the SUT)
        assert coder_prompt.find(_DOCSTRING_INSTRUCTION_WITH_EXAMPLE) < coder_prompt.find("SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:")


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
        ("line1\n# METAMORPHIC_INSERT_POINT\nline3", "\n", "line1\n\n\nline3"), # Empty snippet should replace marker with just its indentation
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
        ("    # METAMORPHIC_INSERT_POINT", "def func():\n        pass", "    def func():\n            pass"),
        # Snippet with internal indentation and existing content indentation
        ("class MyClass:\n    # METAMORPHIC_INSERT_POINT\n    def method(): pass", "    def new_method():\n        pass", "class MyClass:\n    def new_method():\n        pass\n    def method(): pass"),
        # Empty snippet, marker with indentation
        ("    line1\n    # METAMORPHIC_INSERT_POINT\n    line3", "", "    line1\n    \n    line3"), # Empty snippet should replace marker with just its indentation
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


# Fixture for a WorkflowDriver instance
@pytest.fixture
def driver_for_cleaning(tmp_path, mocker):
    context = Context(str(tmp_path))
    mocker.patch.object(WorkflowDriver, '_load_default_policy') # Mock policy loading
    driver = WorkflowDriver(context)
    mocker.patch.object(driver, 'logger', MagicMock()) # Mock logger more explicitly
    return driver

class TestEnhancedSnippetCleaning:
    @pytest.mark.parametrize("input_snippet, expected_output", [
        # Cases with END_OF_CODE_MARKER
        (f"def func():\n    pass\n{END_OF_CODE_MARKER}\nOkay, thanks!", "def func():\n    pass"),
        (f"import os\n{END_OF_CODE_MARKER}", "import os"),
        (f"{END_OF_CODE_MARKER}def func():\n    pass", ""), # Marker at the beginning
        (f"def func():\n    pass\n{END_OF_CODE_MARKER}  ", "def func():\n    pass"), # Marker with trailing whitespace
        (f"```python\ndef func():\n    pass\n{END_OF_CODE_MARKER}\n```\nSome text.", "def func():\n    pass"), # Marker inside fences, then fences stripped

        # Cases with markdown fences (marker not present or after fences)
        ("```python\ndef hello():\n    print('world')\n```", "def hello():\n    print('world')"),
        ("Some text before\n```python\ndef hello():\n    print('world')\n```\nSome text after", "def hello():\n    print('world')"),
        ("```\nimport os\n```", "import os"),
        ("```PYTHON\n# comment\npass\n```", "# comment\npass"),
        (f"No fences, but marker\nprint('ok')\n{END_OF_CODE_MARKER} trailing", "No fences, but marker\nprint('ok')"),

        # Fallback cases (no marker, no standard fences)
        ("Raw code line 1\nRaw code line 2", "Raw code line 1\nRaw code line 2"),
        ("  Stripped raw code  ", "Stripped raw code"),
        ("", ""),
        (None, ""),

        # Test case for the original failure mode:
        ("def _read_targeted_file_content():\n    return \"\"\nOkay, here is the refactored code snippet.",
         "def _read_targeted_file_content():\n    return \"\""), # Assuming no marker, simple strip is fallback
        # Corrected typo here: END_OF_CODE_MARKET -> END_OF_CODE_MARKER
        (f"def _read_targeted_file_content():\n    return \"\"\n{END_OF_CODE_MARKER}\nOkay, here is the refactored code snippet.",
         "def _read_targeted_file_content():\n    return \"\""),
    ])
    def test_enhanced_clean_llm_snippet(self, driver_for_cleaning, input_snippet, expected_output):
        assert driver_for_cleaning._clean_llm_snippet(input_snippet) == expected_output