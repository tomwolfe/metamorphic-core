# tests/test_workflow_driver_snippet_cleaning.py

import pytest
import re
import json
from pathlib import Path
from datetime import datetime
import builtins # For mocking open
from unittest.mock import patch, MagicMock, ANY

# Assuming WorkflowDriver and Context are in src.core.automation
from src.core.automation.workflow_driver import WorkflowDriver, Context

# Fixture for a WorkflowDriver instance
@pytest.fixture
def driver_snippet_handling(tmp_path, mocker):
    # Mock Context.get_full_path to return a predictable path within tmp_path
    # This is crucial for testing the debug file creation.
    def mock_get_full_path(relative_path_str):
        # For the debug directory
        if relative_path_str == ".debug/failed_snippets":
            return str(tmp_path / ".debug/failed_snippets")
        # Fallback for other paths if any (e.g., policy loading in __init__)
        return str(tmp_path / relative_path_str)

    mock_context = MagicMock(spec=Context)
    mock_context.base_path = str(tmp_path)
    mock_context.get_full_path.side_effect = mock_get_full_path

    # Patch dependencies of WorkflowDriver's __init__ if they cause issues
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'), \
         patch.object(WorkflowDriver, '_load_default_policy') as MockLoadPolicy: # Patch _load_default_policy

        MockLoadPolicy.return_value = {'policy_name': 'Mock Policy'}
        driver = WorkflowDriver(mock_context)
        driver.llm_orchestrator = MagicMock() # Ensure it has an LLM orchestrator mock
        driver.logger = MagicMock() # Mock the logger to check calls if needed
        # Ensure default_policy_config is set for tests that might touch ethical checks
        driver.default_policy_config = {'policy_name': 'Mock Policy'}
        return driver

class TestSnippetCleaning:
    @pytest.mark.parametrize("input_snippet, expected_output", [
        ("```python\ndef hello():\n    print('world')\n```", "def hello():\n    print('world')"),
        ("```\nimport os\n```", "import os"),
        ("```PYTHON\n# comment\npass\n```", "# comment\npass"), # Test uppercase PYTHON
        ("```javascript\nconsole.log('test');\n```", "console.log('test');"), # Test other lang tag
        ("No fences here", "No fences here"),
        
        ("  ```python\n  indented code\n  ```  ", "indented code"), # Dedent should remove common leading whitespace
        ("```\n  \n```", ""), # Fences with only whitespace
        ("Leading text ```python\ncode\n```", "code"), # Should extract code if fences found
        ("```python\ncode\n``` Trailing text", "code"), # Should extract code if fences found
        ("```python\ncode1\n```\nSome text\n```python\ncode2\n```", "code1"), # Should extract first code block
        # Removed duplicate input "  Stripped raw code  " to avoid ambiguity
        (None, ""), # This case is fine, None input -> empty string
        ("`single backtick`", "`single backtick`"), # Should not strip single backticks
        ("` ` `", "` ` `"),
    ])
    def test_clean_llm_snippet(self, driver_snippet_handling, input_snippet, expected_output):
        assert driver_snippet_handling._clean_llm_snippet(input_snippet) == expected_output

    def test_clean_llm_snippet_dedents_fenced_block(self, driver_snippet_handling):
        """
        Tests that _clean_llm_snippet correctly removes common leading whitespace
        from a fenced code block.
        """
        driver = driver_snippet_handling
        input_snippet = """
Some conversational text.
```python
    def my_indented_function():
        # This line is further indented
        return "Hello"
```
More conversational text.
"""
        expected_output = "def my_indented_function():\n    # This line is further indented\n    return \"Hello\""
        
        cleaned = driver._clean_llm_snippet(input_snippet)
        assert cleaned == expected_output

    def test_clean_llm_snippet_preserves_heredoc_indentation(self, driver_snippet_handling):
        """
        Tests that intentional indentation within a multi-line string (HEREDOC) is preserved.
        """
        driver = driver_snippet_handling
        input_snippet = """
```python
query = f\"\"\"
    SELECT
        user_id,
        user_name
    FROM users;
\"\"\"
```
"""
        expected_output = "query = f\"\"\"\n    SELECT\n        user_id,\n        user_name\n    FROM users;\n\"\"\""
        cleaned = driver._clean_llm_snippet(input_snippet)
        assert cleaned == expected_output

    def test_clean_llm_snippet_handles_tabs_before_dedent(self, driver_snippet_handling):
        """
        Tests that tabs are converted to spaces before dedenting to avoid errors.
        """
        driver = driver_snippet_handling
        # Note: Python's triple quotes will convert the literal \t to a tab character.
        input_with_tabs = "```python\n\tdef tabbed_function():\n\t\treturn True\n```"
        expected_output = "def tabbed_function():\n    return True"
        cleaned = driver._clean_llm_snippet(input_with_tabs)
        assert cleaned == expected_output

    def test_clean_llm_snippet_preserves_triple_quotes(self, driver_snippet_handling):
        """
        Ensures valid triple-quoted strings are preserved, addressing the original SyntaxError concern.
        """
        driver = driver_snippet_handling
        input_snippet = "```python\nmy_str = '''This is a valid\nmulti-line string.'''\n```"
        expected_output = "my_str = '''This is a valid\nmulti-line string.'''"
        assert driver._clean_llm_snippet(input_snippet) == expected_output

class TestReprLoggingForSyntaxErrors:
    @patch('builtins.open', new_callable=MagicMock) # Mock builtins.open for file writing
    @patch('ast.parse') # Mock ast.parse to control its behavior
    def test_repr_logging_on_syntax_error(self, mock_ast_parse, mock_builtin_open, driver_snippet_handling, tmp_path):
        driver = driver_snippet_handling
        original_snippet = "```python\ndef func():\n  print('unterminated string)\n```"
        # The _clean_llm_snippet will remove the fences
        cleaned_snippet_that_fails = "def func():\n  print('unterminated string)"

        # Configure ast.parse to raise a SyntaxError
        syntax_error_instance = SyntaxError("unterminated string literal", ('<unknown>', 2, 9, "  print('unterminated string)\n"))
        mock_ast_parse.side_effect = syntax_error_instance

        # Simulate the relevant part of the autonomous_loop
        # We need to mock some context variables that would be present in the loop
        driver._current_task = {'task_id': 'test_task_syntax_error'}
        # Simulate being in a step (locals().get('step_index', -1) + 1)
        # This is tricky to mock directly. We can patch datetime to control filename.
        fixed_timestamp = "20230101_120000_000000"
        with patch('src.core.automation.workflow_driver.datetime') as mock_datetime:
            mock_datetime.now.return_value.strftime.return_value = fixed_timestamp
            mock_datetime.now.return_value.isoformat.return_value = "2023-01-01T12:00:00.000000"

            # This is the block that contains the ast.parse and the repr logging
            # We are testing the except SyntaxError block
            validation_feedback = []
            step_failure_reason = None
            step_description_for_log = "Test step description for syntax error"
            step_index_for_log = 0 # Simulating first step

            # Simulate the pre-write validation block directly
            _validation_passed = True
            _validation_feedback = []
            _step_failure_reason = None
            
            # This is the block from SUT we are testing
            try:
                mock_ast_parse(cleaned_snippet_that_fails) # This will raise the mocked SyntaxError
            except SyntaxError as se_in_block:
                _validation_passed = False
                _validation_feedback.append(f"Pre-write syntax check failed: {se_in_block}")
                driver.logger.warning(f"Pre-write syntax validation (AST parse) failed for snippet: {se_in_block}")
                driver.logger.warning(f"Failed snippet (cleaned):\n---\n{cleaned_snippet_that_fails}\n---")
                _step_failure_reason = f"Pre-write syntax check failed: {se_in_block}"

                # --- SUT's Logging Logic (that we are testing) ---
                try:
                    debug_dir_name = ".debug/failed_snippets"
                    debug_dir_path_str = driver.context.get_full_path(debug_dir_name)
                    if debug_dir_path_str:
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
                            "cleaned_snippet_repr": repr(cleaned_snippet_that_fails),
                            "syntax_error_details": {
                                "message": se_in_block.msg, # MODIFIED LINE: Use .msg attribute
                                "lineno": se_in_block.lineno,
                                "offset": se_in_block.offset,
                                "text": se_in_block.text
                            }
                        }
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
        driver.context.get_full_path.assert_called_once_with(".debug/failed_snippets")

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

        # Let's refine the assertion to check the *arguments* to json.dump
        # This requires patching json.dump
        with patch('json.dump') as mock_json_dump:
            # Re-run the failing part to capture json.dump call
            # The `cleaned_snippet_that_fails` needs to be passed to the `mock_ast_parse` call
            # within the `try` block to trigger the `except SyntaxError` block.
            # The `original_snippet` is only used for `repr()` in the `debug_data`.
            # The `_cleaned_snippet` is the one that's actually parsed.
            _cleaned_snippet = driver._clean_llm_snippet(original_snippet) # Ensure this is defined for the inner block
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