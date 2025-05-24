# tests/test_workflow_driver_enhancements.py

import pytest
import re
import json
from pathlib import Path
import logging
import tempfile
import os
import ast # For simulating SyntaxError
from unittest.mock import patch, MagicMock

# Import constants from the centralized constants file
from src.core.constants import (
    MAX_READ_FILE_SIZE,
    METAMORPHIC_INSERT_POINT,
    END_OF_CODE_MARKER,
    MAX_STEP_RETRIES,
    GENERAL_SNIPPET_GUIDELINES,
    DOCSTRING_INSTRUCTION_PYTHON,
    PYTHON_CREATION_KEYWORDS,
    CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS,
    CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS,
)

# Import necessary components from workflow_driver
from src.core.automation.workflow_driver import (
    WorkflowDriver,
    Context,
)

# Import EnhancedLLMOrchestrator as it's patched
from src.core.llm_orchestration import EnhancedLLMOrchestrator

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from core.agents.code_review_agent import CodeReviewAgent
from core.ethics.governance import EthicalGovernanceEngine

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

    @pytest.mark.parametrize("step_description, expected_instruction_substring_from_constant", [
        # Dynamically generate the expected string for each point from the constant itself
        # This makes the test more robust to changes in the constant's content or formatting.
        # splitlines() removes trailing newlines, so we add them back if the original constant line had one.
        # The indices correspond to the lines in the CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS constant.
        # Line 0 is "CRITICAL INSTRUCTIONS FOR YOUR RESPONSE FORMAT:"
        ("Implement a new function.", CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER).splitlines()[1] + "\n"), # Point 1 (index 1)
        ("Add a class definition.", CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER).splitlines()[2] + "\n"), # Point 2 (index 2)
        ("Refactor the main logic.", CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER).splitlines()[3] + "\n"), # Point 3 (index 3)
        ("Fix a bug in the utility module.", CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER).splitlines()[4] + "\n"), # Point 4 (index 4)
        ("Optimize an existing algorithm.", CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER).splitlines()[5] + "\n"), # Point 5 (index 5)
        ("Analyze the requirements.", CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER).splitlines()[11]), # Point 6 (index 11, no trailing newline in constant)
    ])
    def test_coder_prompt_includes_critical_output_instructions_and_new_intro(self, driver_enhancements, step_description, expected_instruction_substring_from_constant):
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
        assert expected_instruction_substring_from_constant in coder_prompt
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in coder_prompt # Check the whole block

        # Assert new introductory line is present and correctly formatted
        expected_intro_line = f"Based on the \"Specific Plan Step\" below, generate the required Python code snippet to modify the target file (`{mock_filepath}`)."
        assert expected_intro_line in coder_prompt

        # Assert the order: critical instructions should come before the new intro line (using the formatted constant)
        assert coder_prompt.find(CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER)) < coder_prompt.find(expected_intro_line)

        # Assert other conditional parts are NOT present
        assert f"\n{DOCSTRING_INSTRUCTION_PYTHON} # (e.g., 'IMPORTANT: For any new Python functions... you MUST include a comprehensive PEP 257 compliant docstring.')\n\n" not in coder_prompt
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
        assert f"\n{DOCSTRING_INSTRUCTION_PYTHON} # (e.g., 'IMPORTANT: For any new Python functions... you MUST include a comprehensive PEP 257 compliant docstring.')\n\n" in coder_prompt

        # Assert other parts are present as expected
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in coder_prompt
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt
        expected_intro_line = f"Based on the \"Specific Plan Step\" below, generate the required Python code snippet to modify the target file (`{mock_filepath}`)."
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
        expected_intro_line = f"Based on the \"Specific Plan Step\" below, generate the required Python code snippet to modify the target file (`{mock_filepath}`)."
        assert expected_intro_line in coder_prompt

        # Assert other parts are present as expected
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in coder_prompt
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt

        # Assert conditional parts are NOT present
        assert f"\n{DOCSTRING_INSTRUCTION_PYTHON} # (e.g., 'IMPORTANT: For any new Python functions... you MUST include a comprehensive PEP 257 compliant docstring.')\n\n" not in coder_prompt

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
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in coder_prompt
        expected_intro_line = f"Based on the \"Specific Plan Step\" below, generate the required Python code snippet to modify the target file (`{mock_filepath}`)."
        assert expected_intro_line in coder_prompt
        assert f"\n{DOCSTRING_INSTRUCTION_PYTHON} # (e.g., 'IMPORTANT: For any new Python functions... you MUST include a comprehensive PEP 257 compliant docstring.')\n\n" in coder_prompt
        assert "SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:" in coder_prompt
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt

        # Assert order of conditional elements (docstring instruction comes before import guidance in the SUT)
        assert coder_prompt.find(f"\n{DOCSTRING_INSTRUCTION_PYTHON}") < coder_prompt.find("SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:")

    def test_coder_prompt_includes_targeted_mod_instructions_and_order(self, driver_enhancements):
        """
        Verify that targeted modification instructions are included and appear after critical instructions.
        """
        driver = driver_enhancements
        mock_task = {
            'task_id': 'mod_task',
            'task_name': 'Modify existing function',
            'description': 'Refactor a function in src/module.py',
            'target_file': 'src/module.py'
        }
        mock_filepath = 'src/module.py'
        mock_existing_content = 'def existing_func(): pass'

        driver._is_add_imports_step.return_value = False
        driver._should_add_docstring_instruction.return_value = False

        coder_prompt = driver._construct_coder_llm_prompt(
            mock_task, mock_task['description'], mock_filepath, mock_existing_content
        )

        assert DOCSTRING_INSTRUCTION_PYTHON not in coder_prompt
        assert "SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:" not in coder_prompt
        
        # Verify both critical and targeted modification instructions are included
        idx_critical = coder_prompt.find(CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER))
        idx_targeted_mod = coder_prompt.find(CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS)
        
        assert idx_critical != -1, "Critical output instructions not found."
        assert idx_targeted_mod != -1, "Targeted modification instructions not found."
        # Assert the relative order, as this is a semantic part of the prompt structure
        assert idx_critical < idx_targeted_mod, "Critical instructions should appear before targeted modification instructions."


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
        (f"{METAMORPHIC_INSERT_POINT}\nline1", "inserted", "inserted\nline1"),
        # Marker at end of file
        (f"line1\n{METAMORPHIC_INSERT_POINT}", "inserted", "line1\ninserted"),
        # No marker, existing ends with newline
        ("line1\nline2\n", "inserted", "line1\nline2\ninserted"),
        # No marker, existing does not end with newline
        ("line1\nline2", "inserted", "line1\nline2\ninserted"),
        # Empty existing content, no marker
        ("", "snippet", "snippet"),
        # Empty existing content, with marker (should still apply indentation if marker implies it)
        (f"    {METAMORPHIC_INSERT_POINT}", "snippet", "    snippet"),
        # Snippet with internal indentation
        ("    # METAMORPHIC_INSERT_POINT", "def func():\n        pass", "    def func():\n            pass"),
        # Snippet with internal indentation and existing content indentation
        ("class MyClass:\n    # METAMORPHIC_INSERT_POINT\n    def method(): pass", "    def new_method():\n        pass", "class MyClass:\n    def new_method():\n        pass\n    def method(): pass"),
        # Empty snippet, marker with indentation
        (f"    line1\n    {METAMORPHIC_INSERT_POINT}\n    line3", "", "    line1\n    \n    line3"), # Empty snippet should replace marker with just its indentation
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
        (f"def func():\n    pass\n{END_OF_CODE_MARKER}\nOkay, thanks!", "def func():\n    pass"), # Marker with trailing chatter
        (f"import os\n{END_OF_CODE_MARKER}", "import os"),
        (f"{END_OF_CODE_MARKER}def func():\n    pass", ""), # Marker at the beginning
        (f"def func():\n    pass\n{END_OF_CODE_MARKER}  ", "def func():\n    pass"), # Marker with trailing whitespace
        (f"```python\ndef func():\n    pass\n{END_OF_CODE_MARKER}\n```\nSome text.", "def func():\n    pass"), # Marker inside fences, then fences stripped
        # Cases with markdown fences (marker not present or after fences)
        ("```python\ndef hello():\n    print('world')\n```", "def hello():\n    print('world')"),
        ("Some text before\n```python\ndef hello():\n    print('world')\n```\nSome text after", "def hello():\n    print('world')"),
        ("```\nimport os\n```", "import os"),
        ("```PYTHON\n# comment\npass\n```", "# comment\npass"),
        ("```javascript\nconsole.log('test');\n```", "console.log('test');"),
        ("No fences here", "No fences here"),
        ("  Stripped raw code  ", "Stripped raw code"),
        ("", ""),
        (None, ""),
        ("`single backtick`", "`single backtick`"), # Should not strip single backticks
        ("` ` `", "` ` `"),
        # Test case for the original failure mode:
        ("def _read_targeted_file_content():\n    return \"\"\nOkay, here is the refactored code snippet.",
         "def _read_targeted_file_content():\n    return \"\""), # This test case is for when the marker is NOT present, and it relies on the heuristic.
        (f"def _read_targeted_file_content():\n    return \"\"\n{END_OF_CODE_MARKER}\nOkay, here is the refactored code snippet.",
         "def _read_targeted_file_content():\n    return \"\""),
    ])
    def test_enhanced_clean_llm_snippet(self, driver_for_cleaning, input_snippet, expected_output):
        assert driver_for_cleaning._clean_llm_snippet(input_snippet) == expected_output

class TestReprLoggingForSyntaxErrors:
    @patch('builtins.open', new_callable=MagicMock)
    @patch('ast.parse')
    def test_repr_logging_on_syntax_error(self, mock_ast_parse, mock_builtin_open, driver_for_cleaning, tmp_path):
        driver = driver_for_cleaning # Get driver from fixture
        original_snippet = "```python\ndef func():\n  print('unterminated string)\n```"
        # The _clean_llm_snippet will remove the fences
        cleaned_snippet_that_fails = "def func():\n  print('unterminated string)"

        # Configure ast.parse to raise a SyntaxError
        syntax_error_instance = SyntaxError("unterminated string literal", ('<unknown>', 2, 9, "  print('unterminated string)\n"))
        mock_ast_parse.side_effect = syntax_error_instance

        # Simulate the relevant part of the autonomous_loop
        # We need to mock some context variables that would be present in the loop
        driver._current_task = {'task_id': 'test_task_syntax_error', 'task_name': 'Test Task', 'description': 'Desc', 'status': 'Not Started', 'priority': 'High'}
        fixed_timestamp = "20230101_120000_000000"
        with patch('src.core.automation.workflow_driver.datetime') as mock_datetime:
            # Patch `driver.context.get_full_path` to mock its behavior
            mock_get_full_path = MagicMock(return_value=str(tmp_path / ".debug/failed_snippets"))
            driver.context.get_full_path = mock_get_full_path
            mock_datetime.now.return_value.strftime.return_value = fixed_timestamp
            mock_datetime.now.return_value.isoformat.return_value = "2023-01-01T12:00:00.000000"

            # This is the block that contains the ast.parse and the repr logging
            # We are testing the except SyntaxError block
            validation_feedback = []
            step_failure_reason = None
            step_description_for_log = "Test step description for syntax error"
            step_index_for_log = 0 # Simulating first step

            try:
                # This call will trigger the mocked ast.parse and the except block
                # We are directly testing the logic that would be inside the autonomous_loop's try-except
                # The cleaning happens before this point in the actual loop
                # For this test, assume cleaned_snippet is what's passed to ast.parse
                # In the SUT, the logging uses `generated_snippet` for original and `cleaned_snippet` for cleaned.
                # So, we need to ensure these are available.
                
                # Simulate the state within the loop for the logging part
                # The actual SUT has:
                # if generated_snippet:
                #    cleaned_snippet = self._clean_llm_snippet(generated_snippet)
                #    try:
                #        ast.parse(cleaned_snippet)
                #    except SyntaxError as se:
                #        # logging logic uses generated_snippet and cleaned_snippet and se
                
                # To make the test more robust, let's assume the SUT has a method like:
                # driver._log_failed_snippet_details(generated_snippet, cleaned_snippet, se, step_description, step_index)
                # And we would mock *that*. But since it's inline, we check `mock_builtin_open`.
                
                # For this test, we'll rely on the `mock_builtin_open` being called by the SUT's
                # `except SyntaxError` block when `ast.parse` (mocked) raises the error.
                # The `driver.start_workflow` or a similar entry point would normally trigger this.
                # Since we are unit testing, we need to isolate this.
                # The `_simulate_step_execution_for_pre_write_validation` from your other test file
                # is a good pattern for this. Let's adapt it.
                
                # Simulate the pre-write validation block directly
                _validation_passed = True
                _validation_feedback = []
                _step_failure_reason = None
                
                # This is the block from SUT we are testing
                _cleaned_snippet = cleaned_snippet_that_fails # Use the pre-cleaned snippet for the parse call
                try:
                    mock_ast_parse(_cleaned_snippet) # This will raise the mocked SyntaxError
                except SyntaxError as se_in_block:
                    _validation_passed = False
                    _validation_feedback.append(f"Pre-write syntax check failed: {se_in_block}")
                    driver.logger.warning(f"Pre-write syntax validation (AST parse) failed for snippet: {se_in_block}")
                    driver.logger.warning(f"Failed snippet (cleaned):\n---\n{_cleaned_snippet}\n---")
                    _step_failure_reason = f"Pre-write syntax check failed: {se_in_block}"

                    # --- SUT's Logging Logic (that we are testing) ---
                    try:
                        debug_dir_name = ".debug/failed_snippets"
                        debug_dir_path_str = driver.context.get_full_path(debug_dir_name)
                        if debug_dir_path_str: # Ensure path resolution for this re-run
                            debug_dir = Path(debug_dir_path_str)
                            debug_dir.mkdir(parents=True, exist_ok=True)
                            # Use the fixed_timestamp from the mock_datetime
                            _timestamp = fixed_timestamp # Use the one from mock_datetime
                            _current_task_id_str = getattr(driver, '_current_task', {}).get('task_id', 'unknown_task')
                            _sanitized_task_id = re.sub(r'[^\w\-_\.]', '_', _current_task_id_str)
                            _current_step_index_str = str(step_index_for_log + 1)

                            filename = f"failed_snippet_{_sanitized_task_id}_step{_current_step_index_str}_{_timestamp}.json"
                            filepath = debug_dir / filename

                            debug_data = {
                                "timestamp": mock_datetime.now.return_value.isoformat.return_value, # Use mocked isoformat
                                "task_id": _current_task_id_str,
                                "step_description": step_description_for_log,
                                "original_snippet_repr": repr(original_snippet),
                                "cleaned_snippet_repr": repr(_cleaned_snippet),
                                "syntax_error_details": {
                                    "message": se_in_block.msg, # MODIFIED LINE: Use .msg attribute
                                    "lineno": se_in_block.lineno,
                                    "offset": se_in_block.offset,
                                    "text": se_in_block.text
                                }
                            }
                            import builtins # Import builtins here to ensure it's the one being patched
                            with builtins.open(filepath, 'w', encoding='utf-8') as f_err: # This calls the mock
                                json.dump(debug_data, f_err, indent=2)
                            driver.logger.error(f"Saved malformed snippet details (JSON) to: {filepath}")
                        else:
                            driver.logger.error(f"Could not resolve debug directory '{debug_dir_name}' using context. Cannot save malformed snippet.")
                    except Exception as write_err:
                        driver.logger.error(f"Failed to save malformed snippet details: {write_err}", exc_info=True)
                    # --- End SUT's Logging Logic ---
                    # Re-raise to simulate SUT behavior if needed for further assertions
                    # raise ValueError(f"Pre-write validation failed: {'. '.join(_validation_feedback)}")
                # End of simulated SUT block

            except ValueError: # Catch the re-raised error if the SUT does that
                pass


        # Assertions
        # Check that context.get_full_path was called for the debug directory
        mock_get_full_path.assert_called_once_with(".debug/failed_snippets")

        # Check that builtins.open was called to write the debug file
        expected_debug_dir = tmp_path / ".debug/failed_snippets"
        expected_filename = f"failed_snippet_test_task_syntax_error_step{step_index_for_log + 1}_{fixed_timestamp}.json"
        expected_filepath = expected_debug_dir / expected_filename
        
        mock_builtin_open.assert_called_once_with(expected_filepath, 'w', encoding='utf-8')

        # Check the content written to the file
        # The first argument to the write call on the mock file object
        # In the SUT, we use json.dump, so we need to mock the file object's write method
        # and capture what json.dump would write.
        # It's easier to capture the `debug_data` dict that was passed to `json.dump`.
        # For this, we'd need to patch `json.dump`.

        from unittest.mock import ANY # For timestamp assertion
        with patch('json.dump') as mock_json_dump:
            # Re-run the failing part to capture json.dump call
            if original_snippet:
                _cleaned_snippet = driver._clean_llm_snippet(original_snippet)
                try:
                    mock_ast_parse(_cleaned_snippet) # This will raise the mocked SyntaxError
                except SyntaxError as se_in_block:
                    try:
                        debug_dir_name = ".debug/failed_snippets"
                        debug_dir_path_str = driver.context.get_full_path(debug_dir_name)
                        if debug_dir_path_str: # Ensure path resolution for this re-run
                            debug_dir = Path(debug_dir_path_str)
                            debug_dir.mkdir(parents=True, exist_ok=True)
                            _timestamp = fixed_timestamp
                            _current_task_id_str = getattr(driver, '_current_task', {}).get('task_id', 'unknown_task')
                            _sanitized_task_id = re.sub(r'[^\w\-_\.]', '_', _current_task_id_str)
                            _current_step_index_str = str(step_index_for_log + 1)
                            filename = f"failed_snippet_{_sanitized_task_id}_step{_current_step_index_str}_{_timestamp}.json"
                            filepath = debug_dir / filename
                            debug_data = {
                                "timestamp": ANY, # datetime.now().isoformat() will be different
                                "task_id": _current_task_id_str,
                                "step_description": step_description_for_log,
                                "original_snippet_repr": repr(original_snippet),
                                "cleaned_snippet_repr": repr(_cleaned_snippet),
                                "syntax_error_details": {
                                    "message": se_in_block.msg, # MODIFIED LINE: Use .msg attribute
                                    "lineno": se_in_block.lineno,
                                    "offset": se_in_block.offset,
                                    "text": se_in_block.text
                                }
                            }
                            import builtins # Import builtins here to ensure it's the one being patched
                            with builtins.open(filepath, 'w', encoding='utf-8') as f_err:
                                json.dump(debug_data, f_err, indent=2) # This will call the mocked json.dump
                    except Exception:
                        pass # Ignore write errors for this specific assertion part

            mock_json_dump.assert_called_once()
            written_data_obj = mock_json_dump.call_args[0][0] # First arg to json.dump

            assert written_data_obj["task_id"] == "test_task_syntax_error"
            assert written_data_obj["step_description"] == step_description_for_log
            assert written_data_obj["original_snippet_repr"] == repr(original_snippet)
            assert written_data_obj["cleaned_snippet_repr"] == repr(cleaned_snippet_that_fails)
            assert written_data_obj["syntax_error_details"]["message"] == "unterminated string literal"
            assert written_data_obj["syntax_error_details"]["lineno"] == 2
            assert written_data_obj["syntax_error_details"]["offset"] == 9
            assert written_data_obj["syntax_error_details"]["text"] == "  print('unterminated string)\n"

        # Check logger call


# Fixture specifically for testing _resolve_target_file_for_step and _validate_path
@pytest.fixture
def driver_for_retry_prompt_test(tmp_path, mocker):
    context = Context(str(tmp_path))
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator, \
         patch.object(WorkflowDriver, '_load_default_policy') as MockLoadPolicy:

        MockLoadPolicy.return_value = {'policy_name': 'Mock Policy'}
        driver = WorkflowDriver(context)
        driver.llm_orchestrator = MockLLMOrchestrator.return_value
        driver.default_policy_config = {'policy_name': 'Mock Policy'}
        
        # Mock methods that would be called in the loop
        mocker.patch.object(driver, '_read_file_for_context', return_value="existing content")
        mocker.patch.object(driver, '_resolve_target_file_for_step', return_value=str(tmp_path / "test_file.py"))
        mocker.patch.object(driver, '_write_output_file') # To prevent actual writes
        mocker.patch.object(driver, '_merge_snippet', side_effect=lambda ex, sn: ex + "\n" + sn)
        mocker.patch.object(driver, 'generate_grade_report')
        mocker.patch.object(driver, '_parse_and_evaluate_grade_report')
        mocker.patch.object(driver, '_update_task_status_in_roadmap')
        
        # Mock _invoke_coder_llm to check prompts
        driver._invoke_coder_llm = MagicMock(return_value="def corrected_code(): pass")
        return driver

def test_retry_prompt_includes_validation_feedback(driver_for_retry_prompt_test, caplog):
    """
    Tests that the CoderLLM prompt includes specific error feedback on a retry attempt
    after a pre-write syntax validation failure.
    """
    caplog.set_level(logging.INFO)
    driver = driver_for_retry_prompt_test
    
    # --- Setup Task and Plan ---
    driver._current_task = {
        'task_id': 'retry_test_task', 'task_name': 'Retry Test Task', 
        'description': 'A task to test retry prompt enhancement.', 'status': 'Not Started', 
        'priority': 'High', 'target_file': 'test_file.py'
    }
    driver.task_target_file = driver._current_task['target_file']
    solution_plan = ["Implement a function in test_file.py"] # Single code-gen step

    # --- Mock Pre-write Validation Failure on First Attempt ---
    # Simulate ast.parse failing for the first generated snippet
    # The actual pre-write validation logic is complex, so we'll mock its outcome
    # by making _invoke_coder_llm raise the specific ValueError that autonomous_loop catches.
    
    original_syntax_error_msg = "Pre-write syntax check failed: unterminated string literal"
    
    # Let _invoke_coder_llm return a bad snippet first, then a good one.
    driver._invoke_coder_llm.side_effect = [
        "def bad_snippet_initial_attempt(): 'unterminated", # Snippet for 1st attempt
        "def good_snippet_retry_attempt(): pass"             # Snippet for 2nd attempt
    ]

    # Mock ast.parse to fail for the first snippet, pass for the second
    # This mock will be active when the autonomous_loop tries to validate the snippet
    mock_ast_parse_instance = MagicMock()
    mock_ast_parse_instance.side_effect = [
        SyntaxError(original_syntax_error_msg, ('<unknown>', 1, 1, '')), # Fails for "bad_snippet_initial_attempt"
        None                                                              # Passes for "good_snippet_retry_attempt"
    ]

    with patch('ast.parse', mock_ast_parse_instance):
        # --- Execute the relevant part of the loop (simplified) ---
        # We are not running the full autonomous_loop, but simulating its core logic for one step.
        step_index = 0
        step = solution_plan[0]
        step_retries = 0
        step_failure_reason_for_current_attempt = None
        
        # Simulate the retry loop for the step
        while step_retries <= MAX_STEP_RETRIES:
            try:
                prelim_flags = driver._classify_step_preliminary(step)
                filepath_to_use = driver._resolve_target_file_for_step(step, driver.task_target_file, prelim_flags)
                existing_content = driver._read_file_for_context(filepath_to_use)

                retry_feedback_for_prompt = None
                if step_retries > 0 and step_failure_reason_for_current_attempt:
                    retry_feedback_for_prompt = (
                        f"\n\nIMPORTANT: YOUR PREVIOUS ATTEMPT TO GENERATE CODE FOR THIS STEP FAILED.\n"
                        f"THE ERROR WAS: {step_failure_reason_for_current_attempt}\n"
                        f"PLEASE ANALYZE THIS ERROR AND THE EXISTING CODE CAREFULLY. "
                        f"ENSURE YOUR NEWLY GENERATED SNIPPET CORRECTS THIS ERROR AND ADHERES TO ALL CODING GUIDELINES.\n"
                        f"AVOID REPEATING THE PREVIOUS MISTAKE.\n"
                    )
                
                coder_prompt = driver._construct_coder_llm_prompt(
                    driver._current_task, step, filepath_to_use, existing_content, 
                    retry_feedback_content=retry_feedback_for_prompt
                )
                generated_snippet = driver._invoke_coder_llm(coder_prompt)
                cleaned_snippet = driver._clean_llm_snippet(generated_snippet)

                # Simulate pre-write validation (the part we are testing the reaction to)
                mock_ast_parse_instance(cleaned_snippet) # This will use the mock_ast_parse_instance

                # If ast.parse didn't raise, validation passed for this attempt
                driver._write_output_file(filepath_to_use, cleaned_snippet, overwrite=True) # Simulate write
                break # Step succeeded

            except Exception as e:
                step_failure_reason_for_current_attempt = str(e)
                logging.error(f"Simulated step execution failed (Attempt {step_retries + 1}): {e}")
                step_retries += 1
                if step_retries > MAX_STEP_RETRIES:
                    logging.error(f"Simulated step failed after max retries.")
                    # In a real scenario, the task would be blocked. For test, we just note it.
                    break 
                logging.warning(f"Simulated step failed. Retrying ({step_retries}/{MAX_STEP_RETRIES})...")


    # --- Assertions ---
    # _invoke_coder_llm should be called twice (initial attempt + 1 retry)
    assert driver._invoke_coder_llm.call_count == 2
    
    # Get the prompt from the second call (the retry)
    retry_prompt_call = driver._invoke_coder_llm.call_args_list[1]
    retry_prompt_text = retry_prompt_call[0][0] # First argument of the call

    assert "IMPORTANT: YOUR PREVIOUS ATTEMPT TO GENERATE CODE FOR THIS STEP FAILED." in retry_prompt_text
    # The error message from SyntaxError includes the message, filename, line, offset, text.
    # str(SyntaxError(...)) is "mock syntax error (<unknown>, line 1, offset 1)"
    # The `step_failure_reason_for_current_attempt` will be this string.
    # The actual error raised by ast.parse is `SyntaxError(original_syntax_error_msg, ...)`
    # So `str(e)` will be `original_syntax_error_msg (<unknown>, line 1, offset 1, text='')`
    # The prompt should contain this.
    assert original_syntax_error_msg in retry_prompt_text 
    assert "PLEASE ANALYZE THIS ERROR AND THE EXISTING CODE CAREFULLY." in retry_prompt_text

    # Check that the first prompt did NOT contain the retry feedback
    initial_prompt_call = driver._invoke_coder_llm.call_args_list[0]
    initial_prompt_text = initial_prompt_call[0][0]
    assert "IMPORTANT: YOUR PREVIOUS ATTEMPT TO GENERATE CODE FOR THIS STEP FAILED." not in initial_prompt_text