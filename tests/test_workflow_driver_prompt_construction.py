# tests/test_workflow_driver_prompt_construction.py
import pytest
from unittest.mock import MagicMock, patch
from src.core.automation.workflow_driver import WorkflowDriver, Context
from src.core.constants import (
    GENERAL_SNIPPET_GUIDELINES,

    DOCSTRING_INSTRUCTION_PYTHON,
    CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS,
    CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION,
    END_OF_CODE_MARKER
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

    def test_prompt_includes_raw_string_and_completeness_guidelines(self, driver_for_prompt_tests):
        driver = driver_for_prompt_tests
        step_description = "Implement a regex pattern using a raw string."
        filepath_to_use = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)

        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )

        assert "Raw Strings and Regex:" in prompt
        assert "ensure they are complete and correctly formatted." in prompt
        assert "Snippet Completeness:" in prompt
        assert "Avoid partial lines or incomplete statements" in prompt
        assert GENERAL_SNIPPET_GUIDELINES in prompt # Ensure base guidelines are still there

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

        assert "CRITICAL PEP 8 ADHERENCE:" in prompt
        assert "Strictly keep lines under 80 characters" in prompt
        assert "Inline comments MUST start with `#` and a single space, and be preceded by at least two spaces" in prompt
        assert "Imports (IMPORTANT - READ CAREFULLY FOR SNIPPETS):" in prompt
        assert "EXCEPTION FOR VALIDATION:" in prompt
        assert "YOU MUST INCLUDE the necessary `from X import Y` statements (e.g., `from pathlib import Path`, `from typing import Optional, List`, `import ast`) AT THE TOP OF YOUR SNIPPET" in prompt
        assert GENERAL_SNIPPET_GUIDELINES in prompt

    def test_prompt_for_new_method_includes_docstring_and_guidelines(self, driver_for_prompt_tests, mocker):
        driver = driver_for_prompt_tests
        step_description = "Add new method process_data to class Processor"
        filepath_to_use = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)

        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=True)

        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )

        assert DOCSTRING_INSTRUCTION_PYTHON in prompt
        assert GENERAL_SNIPPET_GUIDELINES in prompt
        assert "CRITICAL PEP 8 ADHERENCE:" in prompt
        assert "EXCEPTION FOR VALIDATION:" in prompt

    def test_prompt_for_import_step_specific_guidance(self, driver_for_prompt_tests, mocker):
        driver = driver_for_prompt_tests
        step_description = "Add import os and import sys"
        filepath_to_use = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)

        # Mock _is_add_imports_step to return True
        mocker.patch.object(driver, '_is_add_imports_step', return_value=True)
        # Docstring instruction should not apply for simple import additions
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)

        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False # Assuming full context for import analysis for now
        )

        assert "SPECIFIC GUIDANCE FOR IMPORT STATEMENTS:" in prompt
        assert "Provide *only* the new import lines that need to be added." in prompt
        assert GENERAL_SNIPPET_GUIDELINES in prompt # General guidelines should still be present
        assert DOCSTRING_INSTRUCTION_PYTHON not in prompt # Specific docstring instruction should not be there

    def test_prompt_includes_dynamic_import_reminders_for_regex_and_typing(self, driver_for_prompt_tests, mocker):
        """
        Test that dynamic reminders for 're' and 'typing' imports are added
        when step description implies their use.
        """
        driver = driver_for_prompt_tests
        step_description_regex_typing = "Define a function that uses regular expression matching and returns a dictionary with type hints like Dict[str, Any], Optional[Union[str, Callable]]."
        filepath_to_use = driver._resolve_target_file_for_step(step_description_regex_typing, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)

        # Ensure docstring instruction is also potentially triggered to test interplay
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=True)

        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description_regex_typing,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )

        assert "--- IMPORTANT REMINDERS FOR THIS SPECIFIC STEP ---" in prompt
        assert "ensure 'import re' is included at the top of your Python snippet." in prompt
        assert "ensure necessary imports from 'typing' (e.g., 'from typing import Dict, Any, List, Optional, Union, Callable') are included" in prompt
        assert DOCSTRING_INSTRUCTION_PYTHON in prompt # Check other instructions are still present
        assert GENERAL_SNIPPET_GUIDELINES in prompt

    def test_prompt_no_dynamic_reminders_if_keywords_absent(self, driver_for_prompt_tests):
        """
        Test that dynamic reminders are NOT added if keywords are absent.
        """
        driver = driver_for_prompt_tests
        step_description_no_keywords = "Implement a simple calculation."
        filepath_to_use = driver._resolve_target_file_for_step(step_description_no_keywords, driver.task_target_file, {})
        context_for_llm = driver._read_file_for_context(filepath_to_use)

        prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description_no_keywords,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )

        assert "--- IMPORTANT REMINDERS FOR THIS SPECIFIC STEP ---" not in prompt
        assert "import re" not in prompt
        assert "from typing import Dict, Any" not in prompt