import pytest
import re
import json
from pathlib import Path
import logging
import tempfile
import os
import json
from datetime import datetime # Import datetime for TestReprLoggingForSyntaxErrors
import ast # For simulating SyntaxError
from unittest.mock import patch, MagicMock
from unittest.mock import patch, call, ANY # Added call, ANY for assert_has_calls

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
    CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS
)

# Import necessary components from workflow_driver
from src.core.automation.workflow_driver import (
    WorkflowDriver,
    Context,
)

# Import EnhancedLLMOrchestrator as it's patched
from src.core.llm_orchestration import EnhancedLLMOrchestrator

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from src.core.automation.workflow_driver import classify_plan_step # Keep classify_plan_step if used in tests

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(name)s - %(message)s')

logger = logging.getLogger(__name__)

# Fixture specifically for cleaning tests (moved from inside TestEnhancedSnippetCleaning)
@pytest.fixture
def driver_for_cleaning(tmp_path, mocker):
    def mock_get_full_path(relative_path_str):
        if relative_path_str == ".debug/failed_snippets":
            return str(tmp_path / ".debug/failed_snippets")
        return str(tmp_path / relative_path_str)

    mock_context = mocker.MagicMock(spec=Context)
    mock_context.base_path = str(tmp_path)
    mock_context.get_full_path.side_effect = mock_get_full_path

    # Patch _load_default_policy here to prevent it from running the real logic
    mock_load_policy = mocker.patch.object(WorkflowDriver, '_load_default_policy')

    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'):

        driver = WorkflowDriver(mock_context)
        driver.llm_orchestrator = mocker.MagicMock()
        driver.logger = mocker.MagicMock()
        driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure it's set for tests
        return driver
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
    driver.llm_orchestrator = mocker.MagicMock() # Ensure LLM orchestrator is a mock
    driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure policy is loaded

    # Mock internal methods that are called during prompt construction but not directly tested here
    # These mocks will be controlled per test case to simulate different conditions
    mocker.patch.object(driver, '_is_add_imports_step', return_value=False)
    mocker.patch.object(driver, '_find_import_block_end', return_value=0)
    mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)

    yield driver

# Fixture specifically for testing _resolve_target_file_for_step and _validate_path
@pytest.fixture
def driver_for_multi_target_resolution(tmp_path, mocker):
    mock_context = Context(str(tmp_path))
    def mock_get_full_path_side_effect(relative_path_str):
        if not isinstance(relative_path_str, str):
            logger.warning(f"Mock Path validation received invalid input: {relative_path_str}")
            return None

        try:
            if relative_path_str == "":
                 resolved_path = Path(mock_context.base_path).resolve(strict=False)
            else:
                 full_path = (Path(mock_context.base_path) / relative_path_str)
                 resolved_path = full_path.resolve(strict=False)

            resolved_base_path_str = str(Path(mock_context.base_path).resolve(strict=False))
            if not str(resolved_path).startswith(resolved_base_path_str):
                logger.warning(f"Path traversal attempt detected during mock resolution: {relative_path_str} resolved to {resolved_path}")
                return None
            return str(resolved_path)
        except FileNotFoundError:
             logger.debug(f"Mock resolution failed: Path not found for '{relative_path_str}' relative to '{mock_context.base_path}'.")
             return None
        except Exception as e:
            logger.error(f"Error resolving path '{relative_path_str}' relative to '{mock_context.base_path}': {e}", exc_info=True)
            return None

    mock_context_get_full_path = mocker.patch.object(mock_context, 'get_full_path', side_effect=mock_get_full_path_side_effect)

    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'):
        # Patch _load_default_policy BEFORE WorkflowDriver is instantiated
        mock_load_policy = mocker.patch.object(WorkflowDriver, '_load_default_policy')


        driver = WorkflowDriver(mock_context)
        driver.llm_orchestrator = mocker.MagicMock()
        driver.default_policy_config = {'policy_name': 'Mock Policy'}

        mock_context_get_full_path.reset_mock()

        def mock_determine_filepath(step_desc, task_target, flags):
            path_in_step_match = re.search(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_desc, re.IGNORECASE)
            path_in_step = path_in_step_match.group(1) if path_in_step_match else None

            effective_task_target = None
            if task_target and isinstance(task_target, str):
                 targets = [f.strip() for f in task_target.split(',') if f.strip()]
                 if targets:
                     effective_task_target = targets[0]

            filepath_to_use = effective_task_target

            is_code_gen_step = flags.get('is_code_generation_step_prelim', False)
            is_explicit_write_step = flags.get('is_explicit_file_writing_step_prelim', False)

            if filepath_to_use is None and (is_explicit_write_step or is_code_gen_step) and path_in_step:
                 filepath_to_use = path_in_step

            if filepath_to_use is None and (is_explicit_write_step or is_code_gen_step):
                 filepath_from_step_match_fallback = re.search(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_desc, re.IGNORECASE)
                 filepath_to_use = filepath_from_step_match_fallback.group(1) if filepath_from_step_match_fallback else None

            return filepath_to_use

        mocker.patch.object(driver, '_determine_filepath_to_use', side_effect=mock_determine_filepath)
        mocker.patch.object(driver, '_determine_single_target_file', return_value=None)

        yield driver

# Fixture for WorkflowDriver instance
@pytest.fixture
def driver_for_simple_addition_test(tmp_path, mocker):
    mock_context = Context(str(tmp_path))
    
    # Patch dependencies that might be initialized in WorkflowDriver.__init__
    mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
    mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
    mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
    mocker.patch.object(WorkflowDriver, '_load_default_policy') # Mock policy loading

    driver = WorkflowDriver(mock_context)
    driver.llm_orchestrator = MagicMock() 
    # Ensure the logger attribute exists and is a mock for testing logger calls
    driver.logger = MagicMock(spec=logging.Logger) 
    return driver

class TestPhase1_8WorkflowDriverEnhancements:

    @pytest.fixture
    def driver_for_prompt_test(self, tmp_path, mocker):
        mock_context = Context(str(tmp_path))
        # Patch dependencies that might be initialized in WorkflowDriver.__init__
        mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
        mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
        mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
        # Patch logging.getLogger to return a mock logger instance
        mocker.patch('logging.getLogger', autospec=True) 
        mocker.patch.object(WorkflowDriver, '_load_default_policy') # Mock policy loading

        driver = WorkflowDriver(mock_context)
        # Assign the mocked logger instance that logging.getLogger would have returned
        driver.logger = logging.getLogger.return_value 
        driver.llm_orchestrator = MagicMock()
        driver.default_policy_config = {'policy_name': 'Mock Policy'}
        mocker.patch.object(driver, '_is_add_imports_step', return_value=False)
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)
        mocker.patch.object(driver, '_validate_path', side_effect=lambda p: str(Path(driver.context.base_path) / p if p else Path(driver.context.base_path)))
        return driver

    def test_prompt_refinement_for_define_method_signature_step(self, driver_for_prompt_test, mocker):
        """
        Tests that the step description for the CoderLLM is correctly refined
        when a 'Define Method Signature' step is encountered in autonomous_loop,
        and that this refined description is subsequently used in the final prompt.
        This test verifies the exact transformation logic added to autonomous_loop.
        """
        driver = driver_for_prompt_test
        
        original_step_desc = "Define Method Signature: Within the WorkflowDriver class, add the method signature: python def _get_context_type_for_step(self, step_description: str) -> Optional[str]: # Implementation goes here"
        
        # --- Simulate the logic added to autonomous_loop for refining step_description_for_coder ---
        step_description_for_coder = original_step_desc 
        define_sig_pattern = r"Define Method Signature[^\n]*?(?:python\s*)?(def\s+\w+\([^)]*\)(?:\s*->\s*[\w\.\[\], ]+)?)\s*:?" # Robust pattern
        define_sig_match = re.match(define_sig_pattern, original_step_desc, re.IGNORECASE)
        
        assert define_sig_match is not None, "Regex should match the 'Define Method Signature' step description"
        
        if define_sig_match:
            extracted_signature_line = define_sig_match.group(1).strip()
            assert extracted_signature_line == "def _get_context_type_for_step(self, step_description: str) -> Optional[str]"
            if extracted_signature_line.startswith("def "):
                if not extracted_signature_line.endswith(':'): # Colon enforcement
                    extracted_signature_line += ':'
                method_definition_with_pass = f"{extracted_signature_line}\n    pass"
                step_description_for_coder = (
                    f"Insert the following Python method definition into the class. "
                    f"Ensure it is correctly indented and includes a `pass` statement as its body. "
                    f"Output ONLY the complete method definition (signature and 'pass' body).\n"
                    f"Method to insert:\n```python\n{method_definition_with_pass}\n```"
                )
        
        expected_refined_desc = (
            "Insert the following Python method definition into the class. "
            "Ensure it is correctly indented and includes a `pass` statement as its body. "
            "Output ONLY the complete method definition (signature and 'pass' body).\n"
            "Method to insert:\n```python\ndef _get_context_type_for_step(self, step_description: str) -> Optional[str]:\n    pass\n```" # Note the added colon
        )
        assert step_description_for_coder == expected_refined_desc

        # --- Test that _construct_coder_llm_prompt uses this refined description ---
        mock_task_data = {'task_id': 'test_task_sig', 'task_name': 'Test Signature Task', 'description': 'Test signature prompt.', 'target_file': 'src/core/automation/workflow_driver.py'}
        mock_filepath_to_use = "src/core/automation/workflow_driver.py" 
        mock_context_for_llm = "class WorkflowDriver:\n    # METAMORPHIC_INSERT_POINT\n    pass"
        
        final_prompt = driver._construct_coder_llm_prompt(
            task=mock_task_data,
            step_description=step_description_for_coder, 
            filepath_to_use=driver._validate_path(mock_filepath_to_use), 
            context_for_llm=mock_context_for_llm,
            is_minimal_context=False,
            retry_feedback_content=None
        )
        
        assert f"Specific Plan Step:\n{expected_refined_desc}\n" in final_prompt
        assert f"PROVIDED CONTEXT FROM `{driver._validate_path(mock_filepath_to_use)}`" in final_prompt
        assert END_OF_CODE_MARKER in final_prompt

    def test_prompt_refinement_flexible_signature_definition(self, driver_for_prompt_test):
        """
        Tests that the refined prompt logic correctly handles variations in the
        'Define Method Signature' step, such as missing 'python' keyword or trailing colon.
        """
        driver = driver_for_prompt_test
        
        # Variation 1: Missing "python" keyword
        step_desc_no_python = "Define Method Signature: def _flexible_sig_1(self) -> str:"
        # Variation 2: Missing trailing colon
        step_desc_no_colon = "Define Method Signature: python def _flexible_sig_2(self)"
        # Variation 3: Missing "python" and trailing colon
        step_desc_no_python_no_colon = "Define Method Signature: def _flexible_sig_3(self)"

        test_cases = [
            (step_desc_no_python, "def _flexible_sig_1(self) -> str:"),
            (step_desc_no_colon, "def _flexible_sig_2(self):"), # Expect colon to be added
            (step_desc_no_python_no_colon, "def _flexible_sig_3(self):") # Expect colon to be added
        ]

        for original_step_desc, expected_sig_in_prompt_body in test_cases:
            driver.logger.reset_mock() # Reset logger mock for each case
            step_description_for_coder = original_step_desc 
            define_sig_pattern = r"Define Method Signature[^\n]*?(?:python\s*)?(def\s+\w+\([^)]*\)(?:\s*->\s*[\w\.\[\], ]+)?)\s*:?"
            define_sig_match = re.match(define_sig_pattern, original_step_desc, re.IGNORECASE)
            
            assert define_sig_match is not None, f"Regex should match: '{original_step_desc}'"
            
            if define_sig_match:
                extracted_signature_line = define_sig_match.group(1).strip()
                if extracted_signature_line.startswith("def "):
                    if not extracted_signature_line.endswith(':'):
                        extracted_signature_line += ':'
                    method_definition_with_pass = f"{extracted_signature_line}\n    pass"
                    step_description_for_coder = (
                        f"Insert the following Python method definition into the class. "
                        f"Ensure it is correctly indented and includes a `pass` statement as its body. "
                        f"Output ONLY the complete method definition (signature and 'pass' body).\n"
                        f"Method to insert:\n```python\n{method_definition_with_pass}\n```"
                    )
            
            expected_method_insertion_block = f"Method to insert:\n```python\n{expected_sig_in_prompt_body}\n    pass\n```"
            assert expected_method_insertion_block in step_description_for_coder


    def test_prompt_refinement_no_match_uses_original_step(self, driver_for_prompt_test):
        """
        Tests that if the step description does not match the "Define Method Signature"
        pattern, the original step description is used for the CoderLLM.
        """
        driver = driver_for_prompt_test
        original_step_desc = "Implement the full logic for _get_context_type_for_step including regex."
        
        step_description_for_coder = original_step_desc 
        define_sig_pattern = r"Define Method Signature[^\n]*?(?:python\s*)?(def\s+\w+\([^)]*\)(?:\s*->\s*[\w\.\[\], ]+)?)\s*:?"
        define_sig_match = re.match(define_sig_pattern, original_step_desc, re.IGNORECASE)
        
        assert define_sig_match is None, "Regex should NOT match this step description"
        
        if define_sig_match: 
            extracted_signature_line = define_sig_match.group(1).strip()
            if extracted_signature_line.startswith("def "):
                step_description_for_coder = "THIS_SHOULD_NOT_BE_USED"
        
        assert step_description_for_coder == original_step_desc
        for call_args in driver.logger.info.call_args_list:
            assert "Refined step description for CoderLLM" not in call_args[0][0]

        mock_task_data = {'task_id': 'test_task_impl', 'task_name': 'Test Implementation Task', 'description': 'Test implementation prompt.', 'target_file': 'src/core/automation/workflow_driver.py'}
        mock_filepath_to_use = "src/core/automation/workflow_driver.py"
        mock_context_for_llm = "class WorkflowDriver:\n    pass"
        
        final_prompt = driver._construct_coder_llm_prompt(
            task=mock_task_data,
            step_description=step_description_for_coder, 
            filepath_to_use=driver._validate_path(mock_filepath_to_use),
            context_for_llm=mock_context_for_llm,
            is_minimal_context=False,
            retry_feedback_content=None
        )
        
        assert f"Specific Plan Step:\n{original_step_desc}\n" in final_prompt

class TestPhase1_8Features:
    def test_classify_step_preliminary_uses_task_target_file(self, driver_enhancements):
        """
        Test _classify_step_preliminary correctly identifies a code generation step
        when the step description implies code modification and task_target_file is a .py file,
        even if the step description itself doesn't contain a filename.
        """
        driver = driver_enhancements 
        
        step_desc_modify_method = "Modify the main autonomous_loop method to integrate new logic."
        task_target_py_file = "src/core/automation/workflow_driver.py"
        
        prelim_flags = driver._classify_step_preliminary(step_desc_modify_method, task_target_py_file)
        
        assert prelim_flags["is_code_generation_step_prelim"] is True, \
            f"Step '{step_desc_modify_method}' with target '{task_target_py_file}' should be code gen."

        step_desc_conceptual_with_target = "Analyze the WorkflowDriver.autonomous_loop for optimization points."
        prelim_flags_conceptual = driver._classify_step_preliminary(step_desc_conceptual_with_target, task_target_py_file)
        
        assert prelim_flags_conceptual["is_code_generation_step_prelim"] is False, \
            f"Step '{step_desc_conceptual_with_target}' should NOT be code gen despite .py target."
        assert prelim_flags_conceptual["is_research_step_prelim"] is True

    def test_classify_step_preliminary_filepath_in_step_overrides_task_target(self, driver_enhancements):
        """
        Test _classify_step_preliminary uses filepath_from_step if present,
        even if task_target_file is different or not a .py file.
        """
        driver = driver_enhancements
        step_desc_specific_file = "Implement new_helper in utils/helpers.py."
        task_target_other_file = "src/main_module.py" 
        
        prelim_flags = driver._classify_step_preliminary(step_desc_specific_file, task_target_other_file)
        
        assert prelim_flags["is_code_generation_step_prelim"] is True
        assert prelim_flags["filepath_from_step"] == "utils/helpers.py"

        step_desc_md_file = "Update the documentation in README.md."
        task_target_py_file = "src/core/automation/workflow_driver.py"
        prelim_flags_md = driver._classify_step_preliminary(step_desc_md_file, task_target_py_file)

        assert prelim_flags_md["is_code_generation_step_prelim"] is False 
        assert prelim_flags_md["is_explicit_file_writing_step_prelim"] is True
        assert prelim_flags_md["filepath_from_step"] == "README.md"

    def test_research_step_classification(self, driver_enhancements):
        driver = driver_enhancements
        step1 = "Research and identify keywords for src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False


    def test_code_generation_step_classification(self, driver_enhancements):
        driver = driver_enhancements
        step1 = "Implement the new function in src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is True

    def test_explicit_file_writing_step_classification(self, driver_enhancements):
        driver = driver_enhancements
        step1 = "Write the research findings to research_summary.md"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is True

    def test_test_execution_step_classification(self, driver_enhancements):
        driver = driver_enhancements
        step1 = "Run tests for the new feature."
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is False
        assert prelim_flags["is_test_execution_step_prelim"] is True

    def test_conceptual_step_classification(self, driver_enhancements):
        driver = driver_enhancements
        step1 = "Discuss the design approach with the team."
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is False
        assert prelim_flags["is_test_execution_step_prelim"] is False
        assert prelim_flags["is_test_writing_step_prelim"] is False
        assert classify_plan_step(step1) == 'conceptual'


    def test_conceptual_define_step_does_not_overwrite_main_python_target(self, driver_enhancements, tmp_path, caplog, mocker):
        caplog.set_level(logging.INFO)
        driver = driver_enhancements
        resolved_target_path = str(tmp_path / 'src' / 'core' / 'automation' / 'workflow_driver.py')
        mocker.patch.object(driver.context, 'get_full_path', side_effect=lambda path: resolved_target_path if path == 'src/core/automation/workflow_driver.py' else str(Path(tmp_path) / path))


        driver._current_task = {
            'task_id': 'test_conceptual_write', 'task_name': 'Test Conceptual Write',
            'description': 'A test.', 'status': 'Not Started', 'priority': 'High',
            'target_file': 'src/core/automation/workflow_driver.py'
        }
        driver.task_target_file = driver._current_task['target_file']
        plan_step = "Write a define list of keywords for step classification."
        prelim_flags = driver._classify_step_preliminary(plan_step)

        mock_write_output = mocker.patch.object(driver, '_write_output_file')
        mock_resolve_target_file = mocker.patch.object(driver, '_resolve_target_file_for_step', return_value=resolved_target_path)


        filepath_to_use = mock_resolve_target_file(plan_step, driver.task_target_file, prelim_flags)
        content_to_write_decision, overwrite_mode = driver._determine_write_operation_details(plan_step, filepath_to_use, driver.task_target_file, prelim_flags)

        assert content_to_write_decision is None
        mock_write_output.assert_not_called()
        expected_log_message = f"Skipping placeholder write to main Python target {resolved_target_path} for conceptual step: '{plan_step}'."
        assert any(expected_log_message in record.message for record in caplog.records)

class TestIsSimpleAdditionPlanStep:
    @pytest.mark.parametrize("description, expected", [
        # Simple Additions (True)
        ("Add import os to the file.", True),
        ("Add new import for pathlib module.", True),
        ("Insert import typing.List at the top.", True),
        ("Add new method get_user_data to existing class UserProfile.", True),
        ("Add method calculate_sum to class Calculator.", True),
        ("Define new method process_event in class EventHandler.", True),
        ("Implement method render_template in class ViewRenderer.", True),
        ("Define a new constant MAX_USERS = 100.", True),
        ("Add constant API_TIMEOUT with value 30.", True),
        ("Append a log message to the main function.", True),
        ("Insert a print statement for debugging.", True),
        ("Add line to increment counter.", True),
        ("Prepend copyright header to file.", True),
        ("Add a docstring to the process_data function.", True),
        ("Generate docstring for the User class.", True),
        ("Add a comment to explain the algorithm.", True),
        ("Add type hint for the 'name' parameter.", True),

        # Complex Modifications / Refactoring / New Class (False)
        ("Create new class OrderManager.", False),
        ("Create a new class called ShoppingCart.", False),
        ("Refactor the payment processing logic.", False),
        ("Restructure the entire user authentication module.", False),
        ("Modify existing logic in the data validation function.", False),
        ("Update existing method signature for process_order.", False),
        ("Rewrite the file parsing utility.", False),
        ("Design new module for reporting.", False),
        ("Implement new system for notifications.", False),
        ("Overhaul the caching mechanism.", False),
        ("Add a new global function `calculate_statistics` (might need more context).", False),
        ("Implement the core algorithm for pathfinding.", False),
        ("Modify the user interface to include a new button.", False),
        ("Update dependencies in requirements.txt.", False),
        ("Write unit tests for the User model.", False),
        ("Fix bug in the login sequence.", False),
        
        # Ambiguous or Edge Cases (False by default)
        ("Update the file.", False),
        ("Process the data.", False),
        ("Handle user input.", False),
        ("", False),
        ("   ", False),
    ])
    def test_various_descriptions(self, driver_for_simple_addition_test, description, expected):
        assert driver_for_simple_addition_test._is_simple_addition_plan_step(description) == expected

    def test_logging_for_decisions(self, driver_for_simple_addition_test):
        driver = driver_for_simple_addition_test # Use the fixture
        
        # Test simple addition
        driver.logger.reset_mock()
        description_simple = "Add import re."
        driver._is_simple_addition_plan_step(description_simple)
        driver.logger.debug.assert_any_call(
            f"Simple addition pattern 'add import\\b' found in step: '{description_simple}'."
        )
        
        # Test complex modification
        driver.logger.reset_mock()
        description_complex = "Refactor the entire system."
        driver._is_simple_addition_plan_step(description_complex)
        driver.logger.debug.assert_any_call(
            f"Complex pattern 'refactor\\b' found in step: '{description_complex}'. Not a simple addition."
        )
        
        # Test ambiguous case (default false)
        driver.logger.reset_mock()
        description_vague = "Do something vague."
        driver._is_simple_addition_plan_step(description_vague)
        driver.logger.debug.assert_any_call(
            f"No specific simple addition or complex pattern matched for step: '{description_vague}'. Assuming not a simple addition."
        )

class TestPreWriteValidation:
    @pytest.fixture
    def driver_pre_write(self, mocker, tmp_path):
        mock_context = Context(str(tmp_path))
        mock_context_get_full_path = mocker.patch.object(mock_context, 'get_full_path', side_effect=lambda path: str(Path(mock_context.base_path) / path) if path else str(Path(mock_context.base_path)))


        mocker.patch.object(WorkflowDriver, '_load_default_policy') # Patch _load_default_policy here to prevent it from running the real logic during WorkflowDriver init
        with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
             patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
             patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator:


            mock_code_review_agent_instance = MockCodeReviewAgent.return_value
            mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
            mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value

            wd = WorkflowDriver(mock_context)
            wd.code_review_agent = mock_code_review_agent_instance
            wd.ethical_governance_engine = mock_ethical_governance_engine_instance
            wd.llm_orchestrator = mock_llm_orchestrator_instance
            wd.default_policy_config = {'policy_name': 'Mock Policy'}


            wd._current_task_results = {'step_errors': []}
            wd._current_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Mock Description', 'status': 'Not Started', 'priority': 'medium', 'target_file': 'src/mock_file.py'}
            wd.task_target_file = wd._current_task['target_file']

            resolved_target_path = str(Path(tmp_path) / wd.task_target_file)
            mock_resolve_target_file = mocker.patch.object(wd, '_resolve_target_file_for_step', return_value=resolved_target_path)

            mock_write_output = mocker.patch.object(wd, '_write_output_file', return_value=True)

            mock_read_file = mocker.patch.object(wd, '_read_file_for_context', return_value="import os\n\n# METAMORPHIC_INSERT_POINT\n\ndef existing_function():\n    pass")


            mock_context_get_full_path.reset_mock()

            yield {
                'driver': wd,
                'mock_code_review_agent': mock_code_review_agent_instance,
                'mock_ethical_governance_engine': mock_ethical_governance_engine_instance,
                'mock_resolve_target_file': mock_resolve_target_file,
                'mock_write_output': mock_write_output,
                'mock_read_file': mock_read_file,
            }


    def _simulate_step_execution_for_pre_write_validation(self, driver, generated_snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output, mock_code_review_agent, mock_ethical_governance_engine, mocker, step_description="Step 1: Implement code in src/mock_file.py", is_minimal_context=False):
        filepath_to_use = mock_resolve_target_file(step_description, driver.task_target_file, driver._classify_step_preliminary(step_description))

        if filepath_to_use is None:
             logger.error("Simulated _resolve_target_file_for_step returned None.")
             raise ValueError("Resolved file path is None.")
        
        # Patch builtins.open and json.dump for the internal file saving logic within this helper
        mock_open_for_helper = mocker.patch('builtins.open', mocker.mock_open())
        mock_json_dump_for_helper = mocker.patch('json.dump')
        mocker.patch.object(driver, '_get_context_type_for_step', return_value=None) # This line was already here
        
        # Clean the snippet before passing to ast.parse, as the SUT does this
        cleaned_snippet = driver._clean_llm_snippet(generated_snippet)
 
 
        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
        validation_passed = True
        validation_feedback = []
        initial_snippet_syntax_error_details = None # Store details of initial snippet syntax error
        try:
            mock_ast_parse(cleaned_snippet) # Use cleaned_snippet here
            logger.info("Pre-write syntax check (AST parse) passed (isolated).")
        except SyntaxError as se_snippet:
            initial_snippet_syntax_error_details = f"Initial snippet syntax check failed: {se_snippet.msg} on line {se_snippet.lineno} (offset {se_snippet.offset}). Offending line: '{se_snippet.text.strip() if se_snippet.text else 'N/A'}'"
            logger.warning(f"Snippet AST parse check (isolated) failed with SyntaxError: {se_snippet}. This might be acceptable if the snippet integrates correctly. Proceeding to other checks.")
            try:
                debug_dir_name = ".debug/failed_snippets"
                debug_dir_path_str = driver.context.get_full_path(debug_dir_name)
 
                if debug_dir_path_str:
                    debug_dir = Path(debug_dir_path_str)
                    debug_dir.mkdir(parents=True, exist_ok=True)
                    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
                    current_task_id_str = getattr(driver, '_current_task', {}).get('task_id', 'unknown_task')
                    sanitized_task_id = re.sub(r'[^\w\-_\.]', '_', current_task_id_str)
                    current_step_index_str = str(locals().get('step_index', -1) + 1)
 
                    filename = f"failed_snippet_{sanitized_task_id}_step{current_step_index_str}_{timestamp}.json"
                    filepath = debug_dir / filename
 
                    debug_data = {
                        "timestamp": datetime.now().isoformat(),
                        "task_id": current_task_id_str,
                        "step_description": locals().get('step', 'Unknown Step'),
                        "original_snippet_repr": repr(generated_snippet),
                        "cleaned_snippet_repr": repr(cleaned_snippet), # Use cleaned_snippet here
                        "syntax_error_details": {
                            "message": se_snippet.msg,
                            "lineno": se_snippet.lineno,
                            "offset": se_snippet.offset,
                            "text": se_snippet.text
                        }
                    }
 
                    with mock_open_for_helper(filepath, 'w', encoding='utf-8') as f_err:
                        mock_json_dump_for_helper(debug_data, f_err, indent=2)
                    driver.logger.error(f"Saved malformed snippet details (JSON) to: {filepath}")
                else:
                    driver.logger.error(f"Could not resolve debug directory '{debug_dir_name}' using context. Cannot save malformed snippet details (path was None).")
 
            except Exception as write_err:
                driver.logger.error(f"Failed to save malformed snippet details: {write_err}", exc_info=True)
 
        except Exception as e:
            validation_passed = False
            validation_feedback.append(f"Error during pre-write syntax validation (AST parse of snippet): {e}")
            logger.error(f"Error during pre-write syntax validation (AST parse of snippet): {e}", exc_info=True)
            logger.warning(f"Failed snippet (cleaned):\n---\n{cleaned_snippet}\n---") # Use cleaned_snippet here
         
        if validation_passed and driver.default_policy_config:
            try:
                ethical_results = mock_ethical_governance_engine.enforce_policy(
                    cleaned_snippet, # Use cleaned_snippet here
                    driver.default_policy_config,
                    is_snippet=True
                )
                if ethical_results.get('overall_status') == 'rejected':
                    validation_passed = False
                    validation_feedback.append(f"Pre-write ethical check failed: {ethical_results}")
                    logger.warning(f"Pre-write ethical validation failed for snippet: {ethical_results}")
                    logger.warning(f"Failed snippet:\n---\n{cleaned_snippet}\n---") # Use cleaned_snippet here
                else:
                    logger.info("Pre-write ethical validation passed for snippet.")
            except Exception as e:
                validation_passed = False
                validation_feedback.append(f"Error during pre-write ethical validation: {e}")
                logger.error(f"Error during pre-write ethical validation: {e}", exc_info=True)
                logger.warning(f"Failed snippet:\n---\n{cleaned_snippet}\n---") # Use cleaned_snippet here
        elif validation_passed:
            logger.warning("Skipping pre-write ethical validation: Default policy not loaded.")
 
        if validation_passed:
            try:
                style_review_results = mock_code_review_agent.analyze_python(cleaned_snippet) # Use cleaned_snippet here
                critical_findings = [f for f in style_review_results.get('static_analysis', []) if f.get('severity') in ['error', 'security_high']]
                if critical_findings:
                    validation_passed = False
                    validation_feedback.append(f"Pre-write style/security check failed: Critical findings detected.")
                    logger.warning(f"Pre-write style/security validation failed for snippet. Critical findings: {critical_findings}")
                    logger.warning(f"Failed snippet:\n---\n{cleaned_snippet}\n---") # Use cleaned_snippet here
                else:
                    logger.info("Pre-write style/security validation passed for snippet.")
            except Exception as e:
                validation_passed = False
                validation_feedback.append(f"Error during pre-write style/security validation: {e}")
                logger.error(f"Error during pre-write style/security validation: {e}", exc_info=True)
                logger.warning(f"Failed snippet:\n---\n{cleaned_snippet}\n---") # Use cleaned_snippet here
 
        if validation_passed:
            logger.info(f"Snippet-level ethical and style checks passed (or were skipped). Proceeding to pre-merge full file syntax check for {filepath_to_use}.")
 
            try:
                hypothetical_merged_content = driver._merge_snippet(mock_read_file.return_value, cleaned_snippet) # Use cleaned_snippet here
                mock_ast_parse(hypothetical_merged_content)
                logger.info("Pre-merge full file syntax check (AST parse) passed.")
                # If initial_snippet_syntax_error_details existed but full file parse passed,
                # it means the merge context fixed the syntax. Log this.
                if initial_snippet_syntax_error_details:
                    logger.info(f"Initial snippet had a syntax issue ('{initial_snippet_syntax_error_details}'), but it integrated correctly into the full file and passed other pre-write checks.")
                if "Initial snippet syntax check failed" in "".join(validation_feedback):
                    logger.info(f"Initial snippet had a syntax issue, but it integrated correctly into the full file and passed other pre-write checks.")
            except SyntaxError as se_merge:
                validation_passed = False
                validation_feedback.append(f"Pre-merge full file syntax check failed: {se_merge.msg} on line {se_merge.lineno} (offset {se_merge.offset}). Offending line: '{se_merge.text.strip() if se_merge.text else 'N/A'}'")
                logger.warning(f"Pre-merge full file syntax validation failed for {filepath_to_use}: {se_merge}")
                logger.warning(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---")
            except Exception as e_merge:
                validation_passed = False
                validation_feedback.append(f"Error during pre-merge full file syntax validation: {e_merge}")
                logger.error(f"Error during pre-merge full file syntax validation: {e_merge}", exc_info=True)
                logger.warning(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---")
         
        if not validation_passed:
            if initial_snippet_syntax_error_details:
                validation_feedback.insert(0, initial_snippet_syntax_error_details)
            logger.warning(f"Failed snippet (cleaned):\n---\n{cleaned_snippet}\n---") # Use cleaned_snippet here
            error_message_for_retry = f"Pre-write validation failed for snippet targeting {filepath_to_use}. Feedback: {validation_feedback}"
            logger.warning(error_message_for_retry)
            driver._current_task_results['pre_write_validation_feedback'] = validation_feedback
            raise ValueError(f"Pre-write validation failed: {'. '.join(validation_feedback)}")
 
        else:
            logger.info(f"All pre-write validations passed for snippet targeting {filepath_to_use}. Proceeding with actual merge/write.")
            merged_content = driver._merge_snippet(mock_read_file.return_value, cleaned_snippet) # Use cleaned_snippet here
            logger.debug("Snippet merged.")
            logger.info(f"Attempting to write merged content to {filepath_to_use}.")
            try:
                mock_write_output(filepath_to_use, merged_content, overwrite=True)
                logger.info(f"Successfully wrote merged content to {filepath_to_use}.")
 
                try:
                    logger.info(f"Running code review and security scan for {filepath_to_use}...")
                    review_results = mock_code_review_agent.analyze_python(merged_content)
                    driver._current_task_results['code_review_results'] = review_results
                    logger.info(f"Code Review and Security Scan Results for {filepath_to_use}: {review_results}")
                except Exception as review_e:
                    logger.error(f"Error running code review/security scan for {filepath_to_use}: {review_e}", exc_info=True)
                    driver._current_task_results['code_review_results'] = {'status': 'error', 'message': str(review_e)}
 
                if driver.default_policy_config:
                    try:
                        logger.info(f"Running ethical analysis for {filepath_to_use}...")
                        ethical_analysis_results = mock_ethical_governance_engine.enforce_policy(merged_content, driver.default_policy_config)
                        driver._current_task_results['ethical_analysis_results'] = ethical_analysis_results
                        logger.info(f"Ethical Analysis Results for {filepath_to_use}: {ethical_analysis_results}")
                    except Exception as ethical_e:
                        logger.error(f"Error running ethical analysis for {filepath_to_use}: {ethical_e}", exc_info=True)
                        driver._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': str(ethical_e)}
                else:
                    logger.warning("Default ethical policy not loaded. Skipping ethical analysis.")
                    driver._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded.'}
 
            except Exception as e:
                error_msg = f"Failed to write merged content to {filepath_to_use}: {e}"
                logger.error(error_msg, exc_info=True)
                raise e
 
 
    @patch('src.core.automation.workflow_driver.ast.parse')
    def test_pre_write_validation_all_pass(self, mock_ast_parse, driver_pre_write, caplog, mocker):
        caplog.set_level(logging.INFO)
        driver = driver_pre_write['driver'] # Access driver from dict
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file']
        mock_write_output = driver_pre_write['mock_write_output']
 
 
        snippet = "def generated_code(): pass"
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}
        mock_ast_parse.side_effect = [None, None]
 
        resolved_target_path = mock_resolve_target_file.return_value
 
        self._simulate_step_execution_for_pre_write_validation(
            driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file,
            mock_write_output, mock_code_review_agent, mock_ethical_governance_engine, mocker
        )
 
        log_messages = [record.message for record in caplog.records]
        assert any("Pre-write syntax check (AST parse) passed" in msg for msg in log_messages)
        assert any("Pre-write ethical validation passed" in msg for msg in log_messages)
        assert any("Pre-write style/security validation passed for snippet." in msg for msg in log_messages)
        assert any("Pre-merge full file syntax check (AST parse) passed." in msg for msg in log_messages)
        assert any(f"All pre-write validations passed for snippet targeting {resolved_target_path}. Proceeding with actual merge/write." in msg for msg in log_messages)
         
        expected_merged_content = driver._merge_snippet(mock_read_file.return_value, driver._clean_llm_snippet(snippet)) # Use cleaned snippet
        mock_write_output.assert_called_once_with(resolved_target_path, expected_merged_content, overwrite=True)
        mock_code_review_agent.analyze_python.assert_has_calls([call(driver._clean_llm_snippet(snippet)), call(expected_merged_content)]) # Use cleaned snippet
        mock_ethical_governance_engine.enforce_policy.assert_has_calls([call(driver._clean_llm_snippet(snippet), driver.default_policy_config, is_snippet=True), call(expected_merged_content, driver.default_policy_config)]) # Use cleaned snippet
 
        assert not driver._current_task_results['step_errors']
 
    @patch('src.core.automation.workflow_driver.ast.parse')
    def test_pre_write_validation_syntax_fails(self, mock_ast_parse, driver_pre_write, caplog, mocker): # Added mocker
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file']
        mock_write_output = driver_pre_write['mock_write_output']
 
 
        snippet = "def invalid syntax"
        mock_ast_parse.side_effect = [
            SyntaxError("Mock syntax error", ('<string>', 1, 1, 'def invalid syntax')), # For snippet (first call)
            SyntaxError("Mock merged syntax error", ('<string>', 1, 1, 'def invalid syntax')) # For merged content
        ]
 
 
        resolved_target_path = mock_resolve_target_file.return_value
 
        with pytest.raises(ValueError, match=r"Pre-write validation failed: Initial snippet syntax check failed: Mock syntax error on line 1 \(offset 1\)\. Offending line: 'def invalid syntax'"):
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine, mocker # Pass mocker
            )
 
        mock_write_output.assert_not_called()
        log_messages = [record.message for record in caplog.records]
        assert any("Snippet AST parse check (isolated) failed with SyntaxError: Mock syntax error (<string>, line 1)" in msg for msg in log_messages)
        assert any(f"Pre-merge full file syntax validation failed for {resolved_target_path}: Mock merged syntax error (<string>, line 1)" in msg for msg in log_messages)
        assert not any(f"All pre-write validations passed for snippet targeting {resolved_target_path}. Proceeding with actual merge/write." in msg for msg in log_messages)
        assert not any(f"Pre-write validation passed for snippet targeting {resolved_target_path}. Proceeding with merge/write." in msg for msg in log_messages) # This line was already correct
        assert any(f"Failed snippet (cleaned):\n---\n{driver._clean_llm_snippet(snippet)}\n---" in msg for msg in log_messages) # Changed to (cleaned)
        mock_code_review_agent.analyze_python.assert_called_once_with(driver._clean_llm_snippet(snippet)) # Use cleaned snippet
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(driver._clean_llm_snippet(snippet), driver.default_policy_config, is_snippet=True) # Use cleaned snippet
        assert mock_code_review_agent.analyze_python.call_count == 1
        assert mock_ethical_governance_engine.enforce_policy.call_count == 1
 
 
    @patch('src.core.automation.workflow_driver.ast.parse')
    def test_pre_write_validation_ethical_fails(self, mock_ast_parse, driver_pre_write, caplog, mocker): # Added mocker
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file']
        mock_write_output = driver_pre_write['mock_write_output']
 
 
        snippet = "def generated_code(): pass"
        mock_ast_parse.return_value = True
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}
 
        resolved_target_path = mock_resolve_target_file.return_value
 
        with pytest.raises(ValueError, match=r"Pre-write validation failed: Pre-write ethical check failed:"):
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine, mocker # Pass mocker
            )
 
        mock_write_output.assert_not_called()
        log_messages = [record.message for record in caplog.records]
        assert any("Pre-write ethical validation failed for snippet" in msg for msg in log_messages) # This line was already correct
        assert any(f"Failed snippet (cleaned):\n---\n{driver._clean_llm_snippet(snippet)}\n---" in msg for msg in log_messages) # Changed to (cleaned)
        assert any(re.search(r"Pre-write ethical check failed: {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}", record.message) for record in caplog.records)
        mock_code_review_agent.analyze_python.assert_not_called()
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(driver._clean_llm_snippet(snippet), driver.default_policy_config, is_snippet=True) # Use cleaned snippet
 
 
    @patch('src.core.automation.workflow_driver.ast.parse')
    def test_pre_write_validation_style_fails(self, mock_ast_parse, driver_pre_write, caplog, mocker): # Added mocker
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file']
        mock_write_output = driver_pre_write['mock_write_output']
 
 
        snippet = "def generated_code(): pass"
        mock_ast_parse.return_value = True
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        mock_code_review_agent.analyze_python.return_value = {'status': 'failed', 'static_analysis': [{'severity': 'error', 'code': 'E302', 'message': 'expected 2 blank lines'}]}
 
        resolved_target_path = mock_resolve_target_file.return_value
 
        with pytest.raises(ValueError, match=r"Pre-write validation failed: Pre-write style/security check failed:"):
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine, mocker # Pass mocker
            )
 
        mock_write_output.assert_not_called()
        log_messages = [record.message for record in caplog.records]
        assert any("Pre-write style/security validation failed for snippet" in msg for msg in log_messages)
        assert any(f"Failed snippet (cleaned):\n---\n{driver._clean_llm_snippet(snippet)}\n---" in msg for msg in log_messages) # Changed to (cleaned)
        assert any(f"Pre-write validation failed for snippet targeting {resolved_target_path}. Feedback: ['Pre-write style/security check failed: Critical findings detected.']" in record.message for record in caplog.records)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(driver._clean_llm_snippet(snippet), driver.default_policy_config, is_snippet=True) # Use cleaned snippet
        mock_code_review_agent.analyze_python.assert_called_once_with(driver._clean_llm_snippet(snippet)) # Use cleaned snippet
 
    @patch('src.core.automation.workflow_driver.ast.parse')
    def test_pre_write_validation_full_file_syntax_fails(self, mock_ast_parse, driver_pre_write, caplog, mocker):
        caplog.set_level(logging.INFO)
        driver = driver_pre_write['driver'] # This line was already correct
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file']
        mock_write_output = driver_pre_write['mock_write_output']
 
        snippet = "    def new_method():\n        pass"
        existing_content = "import os\n\n# METAMORPHIC_INSERT_POINT\n\ndef existing_function():\n    pass"
 
        mock_read_file.return_value = existing_content
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}
 
        def ast_parse_side_effect_func(code_str):
            if ast_parse_side_effect_func.call_count == 0:
                ast_parse_side_effect_func.call_count += 1
                return None
            else:
                expected_merged_prefix = "import os\n\ndef new_method():\n        pass\n\ndef existing_function():\n    pass"
                if not code_str.startswith(expected_merged_prefix):
                    raise AssertionError(f"Expected merged content for second AST parse call, got: {code_str[:100]}...")
                raise SyntaxError("unexpected indent", ('<string>', 3, 5, "    def new_method():\n"))
        ast_parse_side_effect_func.call_count = 0
        mock_ast_parse.side_effect = ast_parse_side_effect_func
 
        resolved_target_path = mock_resolve_target_file.return_value
 
        with pytest.raises(ValueError, match=r"Pre-write validation failed: Pre-merge full file syntax check failed:"):
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine, mocker # Pass mocker
            )
 
        mock_write_output.assert_not_called()
 
        log_messages = [record.message for record in caplog.records]
        assert any("Pre-write syntax check (AST parse) passed (isolated)." in msg for msg in log_messages)
        assert any("Pre-merge full file syntax validation failed for" in msg for msg in log_messages)
        hypothetical_merged_content = "import os\n\ndef new_method():\n        pass\n\ndef existing_function():\n    pass"
        assert any(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---" in msg for msg in log_messages)
        assert any(f"Pre-merge full file syntax validation failed for {resolved_target_path}: unexpected indent" in msg for msg in log_messages)
 
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(driver._clean_llm_snippet(snippet), driver.default_policy_config, is_snippet=True) # Use cleaned snippet
        mock_code_review_agent.analyze_python.assert_called_once_with(driver._clean_llm_snippet(snippet)) # Use cleaned snippet
 
        assert mock_ethical_governance_engine.enforce_policy.call_count == 1
        assert mock_code_review_agent.analyze_python.call_count == 1
class TestRetryPromptEnhancement:
    @pytest.fixture(autouse=True)
    def setup_driver(self, tmp_path, mocker):
        context = Context(str(tmp_path))
        mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
        mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
        mock_llm_orchestrator_patcher = mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
        mocker.patch.object(WorkflowDriver, '_load_default_policy')
 
        driver = WorkflowDriver(context)
        driver.llm_orchestrator = mock_llm_orchestrator_patcher.return_value
        driver.default_policy_config = {'policy_name': 'Mock Policy'}
         
        driver._current_task = {
            'task_id': 'prompt_refinement_test_task',
            'task_name': 'Prompt Refinement Test Task',
            'description': 'A task to test prompt refinement.',
            'target_file': 'src/module.py'
        }
        driver.task_target_file = 'src/module.py'
 
        mocker.patch.object(driver, '_resolve_target_file_for_step', return_value=str(tmp_path / driver._current_task['target_file']))
        mocker.patch.object(driver, '_read_file_for_context', return_value="existing content")
        mocker.patch.object(driver, '_is_add_imports_step', return_value=False)
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False)
 
        yield driver
 
    def test_coder_prompt_includes_general_guidelines_no_import(self, setup_driver):
        """Verify general guidelines are included in the prompt for a regular code gen step."""
        driver = setup_driver
        step_description = "Implement a new function."
        filepath = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_content = driver._read_file_for_context(filepath)
 
        coder_prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath,
            context_for_llm=context_content,
            is_minimal_context=False
        )
 
        # Assertions using the actual constant imported from SUT
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt
        # Assert on key phrases from the guidelines to ensure content integrity
        assert "Ensure all string literals are correctly terminated" in coder_prompt
        assert "Pay close attention to Python's indentation rules" in coder_prompt
        assert "Generate complete and runnable Python code snippets" in coder_prompt
        assert "If modifying existing code, ensure the snippet integrates seamlessly" in coder_prompt
        assert coder_prompt.count(GENERAL_SNIPPET_GUIDELINES) == 1 # Ensure no duplication
 
    def test_coder_prompt_includes_general_guidelines_with_import(self, setup_driver, mocker):
        """Verify general guidelines are included and not duplicated for an import step."""
        driver = setup_driver
        step_description = "Add import statements."
        filepath = driver._resolve_target_file_for_step(step_description, driver.task_target_file, {})
        context_content = driver._read_file_for_context(filepath)
 
        # Mock _is_add_imports_step to return True for this test case
        mocker.patch.object(driver, '_is_add_imports_step', return_value=True)
 
        # Call the SUT method directly, simulating an import step
        coder_prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath,
            context_for_llm=context_content,
            is_minimal_context=False
        )
 
        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt
        assert "You are adding import statements." in coder_prompt # Specific to import steps
        assert coder_prompt.count(GENERAL_SNIPPET_GUIDELINES) == 1
class TestMergeSnippetLogic:
    @pytest.fixture(autouse=True)
    def setup_driver(self, tmp_path, mocker):
        context = Context(str(tmp_path))
        mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
        mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
        mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
        mocker.patch.object(WorkflowDriver, '_load_default_policy')
 
        driver = WorkflowDriver(context)
        driver.default_policy_config = {'policy_name': 'Mock Policy'}
        yield driver
 
    @pytest.mark.parametrize("existing_content, snippet, expected_merged_content", [
        ("def func():\n    # METAMORPHIC_INSERT_POINT\n    pass", "new_line = 1", "def func():\n    new_line = 1\n    pass"),
        ("def func():\n    # METAMORPHIC_INSERT_POINT\n    pass", "line1\nline2", "def func():\n    line1\n    line2\n    pass"),
        ("# METAMORPHIC_INSERT_POINT\ndef func(): pass", "import os", "import os\ndef func(): pass"),
        ("def func():\n    pass\n# METAMORPHIC_INSERT_POINT", "return True", "def func():\n    pass\nreturn True"),
        ("class MyClass:\n    def method(self):\n        # METAMORPHIC_INSERT_POINT\n        print('done')",
         "self.value = 10\nprint('init')",
         "class MyClass:\n    def method(self):\n        self.value = 10\n        print('init')\n        print('done')"),
        ("line1\nline2", "appended", "line1\nline2\nappended"),
        ("line1", "appended", "line1\nappended"),
        ("def func():\n    x = 1 # METAMORPHIC_INSERT_POINT\n    pass", "", "def func():\n    x = 1\n    \n    pass"),
        ("def func():\n    # METAMORPHIC_INSERT_POINT\n    pass", "    inner_line = 1", "def func():\n    inner_line = 1\n    pass"),
        ("def func():\n    x = 1 # METAMORPHIC_INSERT_POINT\n    pass", "y = 2", "def func():\n    x = 1\n    y = 2\n    pass"),
        ("def func():\n    x = 1 # METAMORPHIC_INSERT_POINT\n    pass", "lineA\nlineB", "def func():\n    x = 1\n    lineA\n    lineB\n    pass"),
    ])
    def test_merge_snippet_with_indentation_logic(self, setup_driver, existing_content, snippet, expected_merged_content):
        driver = setup_driver
        merged_content = driver._merge_snippet(existing_content, snippet)
        assert merged_content == expected_merged_content
 
    def test_merge_snippet_no_marker_append_behavior(self, setup_driver):
        driver = setup_driver
        existing = "line1\nline2"
        snippet = "new_content"
        expected = "line1\nline2\nnew_content"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected
 
    def test_merge_snippet_no_marker_existing_no_newline(self, setup_driver):
        driver = setup_driver
        existing = "line1"
        snippet = "new_content"
        expected = "line1\nnew_content"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected
 
class TestEnhancedSnippetCleaning:
    @pytest.fixture
    def driver_for_cleaning(tmp_path, mocker):
        def mock_get_full_path(relative_path_str):
            if relative_path_str == ".debug/failed_snippets":
                return str(tmp_path / ".debug/failed_snippets")
            return str(tmp_path / relative_path_str)
 
        mock_context = mocker.MagicMock(spec=Context)
        mock_context.base_path = str(tmp_path)
        mock_context.get_full_path.side_effect = mock_get_full_path
 
        with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
             patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
             patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'), \
             patch.object(WorkflowDriver, '_load_default_policy') as MockLoadPolicy:
 
            MockLoadPolicy.return_value = {'policy_name': 'Mock Policy'}
            driver = WorkflowDriver(mock_context)
            driver.llm_orchestrator = mocker.MagicMock()
            driver.logger = mocker.MagicMock()
            driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure it's set for tests
            return driver
 
    @pytest.mark.parametrize("input_snippet, expected_output", [
        (f"def func():\n    pass\n{END_OF_CODE_MARKER}\nOkay, thanks!", "def func():\n    pass"),
        (f"import os\n{END_OF_CODE_MARKER}", "import os"),
        (f"{END_OF_CODE_MARKER}def func():\n    pass", ""),
        (f"def func():\n    pass\n{END_OF_CODE_MARKER}  ", "def func():\n    pass"),
        (f"```python\ndef func():\n    pass\n{END_OF_CODE_MARKER}\n```\nSome text.", "def func():\n    pass"),
        ("```python\ndef hello():\n    print('world')\n```", "def hello():\n    print('world')"),
        ("Some text before\n```python\ndef hello():\n    print('world')\n```\nSome text after", "def hello():\n    print('world')"),
        ("```\nimport os\n```", "import os"),
        ("```PYTHON\n# comment\npass\n```", "# comment\npass"),
        ("```javascript\nconsole.log('test');\n```", "console.log('test');"),
        ("No fences here", "No fences here"),
        ("  Stripped raw code  ", "Stripped raw code"),
        # Removed duplicate input "  Stripped raw code  " to avoid ambiguity
        (None, ""), # This case is fine, None input -> empty string
        ("`single backtick`", "`single backtick`"),
        ("` ` `", "` ` `"),
        ("def _read_targeted_file_content():\n    return \"\"\nOkay, here is the refactored code snippet.",
         "def _read_targeted_file_content():\n    return \"\""),
        (f"def _read_targeted_file_content():\n    return \"\"\n{END_OF_CODE_MARKER}\nOkay, here is the refactored code snippet.",
         "def _read_targeted_file_content():\n    return \"\""),
    ])
    def test_enhanced_clean_llm_snippet(self, driver_for_cleaning, input_snippet, expected_output):
        assert driver_for_cleaning._clean_llm_snippet(input_snippet) == expected_output
 
class TestReprLoggingForSyntaxErrors:
    @patch('json.dump') # Mock json.dump to capture its arguments
    @patch('builtins.open', new_callable=MagicMock) # Mock builtins.open for file writing
    @patch('ast.parse') # Mock ast.parse to control its behavior
    def test_repr_logging_on_syntax_error(self, mock_ast_parse, mock_builtin_open, mock_json_dump, driver_for_cleaning, tmp_path, mocker):
        driver = driver_for_cleaning # Get driver from fixture
        original_snippet = "```python\ndef func():\n  print('unterminated string)\n```"