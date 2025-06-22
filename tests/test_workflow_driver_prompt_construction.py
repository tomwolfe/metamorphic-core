# tests/test_workflow_driver_prompt_construction.py
import pytest
from unittest.mock import MagicMock, patch
from src.core.automation.workflow_driver import WorkflowDriver, Context
from src.core.constants import (
    GENERAL_SNIPPET_GUIDELINES,
    DOCSTRING_INSTRUCTION_PYTHON,
    CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS,
    CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION,
    END_OF_CODE_MARKER,
    GENERAL_PYTHON_DOCSTRING_REMINDER # Import the new constant
)
import os
from pathlib import Path

@pytest.fixture
def driver_for_prompt_tests(tmp_path, mocker):
    context = Context(str(tmp_path))
    # Mock dependencies that WorkflowDriver's __init__ or methods might use
    mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
    mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
    mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
    mocker.patch.object(WorkflowDriver, '_load_default_policy') # Mock policy loading

    driver = WorkflowDriver(context)
    driver.llm_orchestrator = mocker.MagicMock() # Ensure LLM orchestrator is a mock
    driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure policy is loaded

    # Mock task data for context within the driver
    driver._current_task = {
        'task_id': 'prompt_test_task',
        'task_name': 'Prompt Test Task',
        'description': 'A task to test prompt construction.',
        'target_file': 'src/module.py'
    }
    driver.task_target_file = 'src/module.py'

    mock_resolved_target_path = str(tmp_path / driver._current_task['target_file'])
    mocker.patch.object(driver, '_resolve_target_file_for_step', return_value=mock_resolved_target_path)
    mocker.patch.object(driver, '_read_file_for_context', return_value="existing file content")
    mocker.patch.object(driver, '_is_add_imports_step', return_value=False)
    mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)
    # Mock _validate_path as it's called by _construct_coder_llm_prompt indirectly
    mocker.patch.object(driver, '_validate_path', side_effect=lambda p: str(Path(driver.context.base_path) / p) if p else str(Path(driver.context.base_path)))
    
    return driver

class TestWorkflowDriverPromptConstruction:

    def test_prompt_includes_updated_general_guidelines(self, driver_for_prompt_tests):
        driver = driver_for_prompt_tests
        step_description = "Implement a new utility function."
        # Resolve path using the mocked _resolve_target_file_for_step
        filepath_to_use = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)

        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )

        # Assertions for the significantly enhanced Raw Strings and Regular Expressions guideline
        assert "Raw Strings and Regular Expressions (CRITICAL):" in prompt
        assert "CRITICAL that they are correctly formatted and fully terminated." in prompt
        # The test assertion needs to match the literal string that will be in the prompt (without the trailing newline) from constants.py
        assert "    - **Common Error:** Avoid generating incomplete raw string literals like `r\\\"^\\\\s*` (missing closing quote) or `r'my_pattern\\\\'` (trailing unescaped backslash). These are common failure modes for LLMs." in prompt
        assert "    - **Example of Correct Usage:** `pattern = r\\\"^\\\\s*\\\"` or `path = r'C:\\\\Users\\\\Name\\\\Docs'`" in prompt
        assert "    - **Example of Incorrect Usage (AVOID):** `r\\\"^\\\\s*` (missing closing quote) or `r'path\\\\'` (trailing unescaped backslash)." in prompt

        assert GENERAL_SNIPPET_GUIDELINES in prompt

    def test_prompt_for_new_method_includes_docstring_and_guidelines(self, driver_for_prompt_tests, mocker):
        driver = driver_for_prompt_tests
        step_description = "Add new method process_data to class Processor"
        filepath_to_use = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)
    
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=True) # Ensure this returns True for the test
    
        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )

        assert "IMPORTANT: For new Python functions, methods, or classes, if you are generating the *full implementation* (including the body)," in prompt
        assert GENERAL_SNIPPET_GUIDELINES in prompt

    def test_prompt_includes_general_docstring_reminder_for_py_modifications(self, driver_for_prompt_tests, mocker):
        """
        Test that GENERAL_PYTHON_DOCSTRING_REMINDER is included for Python file modifications
        when DOCSTRING_INSTRUCTION_PYTHON is not triggered.
        """
        driver = driver_for_prompt_tests
        step_description = "Refactor internal logic of existing_function in module.py."
        filepath_to_use = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)

        # Ensure _should_add_docstring_instruction returns False (not a "creation" step)
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)

        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath_to_use, # This is 'src/module.py'
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )

        assert DOCSTRING_INSTRUCTION_PYTHON not in prompt
        assert GENERAL_PYTHON_DOCSTRING_REMINDER in prompt
        assert "significantly modified to implement this step" in GENERAL_PYTHON_DOCSTRING_REMINDER

    def test_prompt_skips_docstring_reminder_for_non_code_py_files(self, driver_for_prompt_tests, mocker):
        """
        Test that the general docstring reminder is NOT included for non-code Python files
        like __init__.py.
        """
        driver = driver_for_prompt_tests
        step_description = "Update config settings in __init__.py"
        
        # Override the mocked target file for this specific test
        driver._current_task['target_file'] = 'src/__init__.py'
        
        # Patch _resolve_target_file_for_step specifically for this test
        # to return the desired __init__.py path. Use pathlib.Path for path joining.
        mock_init_py_path = str(Path(driver.context.base_path) / 'src/__init__.py')
        
        # The filepath_to_use argument to _construct_coder_llm_prompt should be the desired path
        filepath_for_prompt = mock_init_py_path
    
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)
    
        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath_for_prompt, # Use the correctly mocked path here
            context_for_llm="",
            is_minimal_context=False
        )
    
        assert GENERAL_PYTHON_DOCSTRING_REMINDER not in prompt
        assert DOCSTRING_INSTRUCTION_PYTHON not in prompt