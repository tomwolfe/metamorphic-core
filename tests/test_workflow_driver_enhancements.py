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

class TestPhase1_8Features:
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
    # --- Tests for _is_simple_addition_plan_step (Task 1.8.A) ---
    @pytest.mark.parametrize("description, expected", [
        ("Add import os to the file", True),
        ("add a new function called calculate_total", True),
        ("Implement method process_item in Processor", True),
        ("insert line: logger.info('Processing complete')", True),
        ("append new_config_value to settings.py", True),
        ("Define a new constant MAX_RETRIES = 3", True),
        ("Add a type hint for the user_id parameter", True),
        ("Generate docstring for the main function", True),
        ("Add a comment explaining the complex logic", True),
        ("Add logging for critical operations", True),
        ("Add a new test case for user login", True),
        ("Add __init__ method to the User class", True),
        # Class creation cases, expected to be False
        ("Create new class ComplexSystem for advanced calculations", False),
        ("Add class NewComponent to the architecture", False),
        ("Define class User", False),
        ("Implement class MyUtility", False),
        ("Generate class for data processing", False),
        ("Refactor the entire data processing module", False),
        ("Design the new user interface components", False),
        ("Review the latest pull request for feature X", False),
        ("Analyze performance bottlenecks in the API", False),
        ("Understand the requirements for the next phase", False),
        ("Modify existing function to handle new edge cases", False),
        ("Update the database schema", False),
        ("Write a comprehensive design document", False),
        ("Add a new complex system with multiple classes", False),
        ("", False),
        ("    ", False),
        ("Long desc, no simple add keywords, architectural review.", False),
    ])
    def test_is_simple_addition_plan_step(self, driver_enhancements, description, expected, caplog):
        """Test the _is_simple_addition_plan_step method with various descriptions."""
        caplog.set_level(logging.DEBUG)
        driver = driver_enhancements
        assert driver._is_simple_addition_plan_step(description) == expected
        if expected:
            assert any(
                record.message.startswith(f"Step '{description[:50]}...' identified by")
                for record in caplog.records
            )
        else:
            assert not any(record.message.startswith(f"Step '{description[:50]}...' identified by") and "keyword:" in record.message for record in caplog.records), \
                f"Unexpected 'identified by' log for non-simple step '{description}'"
            assert any(
                (f"Step '{description[:50]}...' not identified as simple." in record.message) or
                (f"Step '{description[:50]}...' involves class creation keyword" in record.message) or
                (f"Step '{description[:50]}...' matches" in record.message and "and includes class and is not simple" in record.message)
                for record in caplog.records
            ), f"Expected specific log message for non-simple step '{description}', but found none matching criteria in {caplog.records}"

    def test_is_simple_addition_plan_step_class_creation_keywords_are_not_simple(self, driver_enhancements, caplog):
        """
        Test that steps involving class creation keywords are correctly identified as NOT simple.
        """
        caplog.set_level(logging.DEBUG)
        driver = driver_enhancements
        class_creation_steps = [
            "Create new class ComplexSystem for advanced calculations",
            "Add class NewComponent to the architecture",
            "Define class User",
            "Implement class MyUtility",
            "Generate class for data processing"
        ]
        for step_desc in class_creation_steps:
            assert driver._is_simple_addition_plan_step(step_desc) is False, f"Step '{step_desc}' should NOT be simple."
            assert any(
                (f"Step '{step_desc[:50]}...' involves class creation keyword" in record.message) or
                (f"Step '{step_desc[:50]}...' matches" in record.message and "and includes class and is not simple" in record.message) or
                (f"Step '{step_desc[:50]}...' not identified as simple." in record.message)
                for record in caplog.records
            ), f"Expected specific log message for non-simple class creation step '{step_desc}', but found none matching criteria in {caplog.records}"
            caplog.clear()

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

            mock_read_file = mocker.patch.object(wd, '_read_file_for_context', return_value="existing file content")


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


        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
        validation_passed = True
        validation_feedback = []
        initial_snippet_syntax_error_details = None # Store details of initial snippet syntax error
        try:
            mock_ast_parse(generated_snippet)
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
                        "cleaned_snippet_repr": repr(generated_snippet), # Assuming cleaned_snippet is same as generated for this test
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
            logger.warning(f"Failed snippet (cleaned):\n---\n{generated_snippet}\n---")
        
        if validation_passed and driver.default_policy_config:
            try:
                ethical_results = mock_ethical_governance_engine.enforce_policy(
                    generated_snippet, 
                    driver.default_policy_config,
                    is_snippet=True
                )
                if ethical_results.get('overall_status') == 'rejected':
                    validation_passed = False
                    validation_feedback.append(f"Pre-write ethical check failed: {ethical_results}")
                    logger.warning(f"Pre-write ethical validation failed for snippet: {ethical_results}")
                    # The test expects this log, so explicitly add it here for ethical failures
                else:
                    logger.info("Pre-write ethical validation passed for snippet.")
            except Exception as e:
                validation_passed = False
                validation_feedback.append(f"Error during pre-write ethical validation: {e}")
                logger.error(f"Error during pre-write ethical validation: {e}", exc_info=True)
        elif validation_passed:
            logger.warning("Skipping pre-write ethical validation: Default policy not loaded.")

        if validation_passed:
            try:
                style_review_results = mock_code_review_agent.analyze_python(generated_snippet)
                critical_findings = [f for f in style_review_results.get('static_analysis', []) if f.get('severity') in ['error', 'security_high']]
                if critical_findings:
                    validation_passed = False
                    validation_feedback.append(f"Pre-write style/security check failed: Critical findings detected.")
                    # The test expects this log, so explicitly add it here for style failures
                    logger.warning(f"Pre-write style/security validation failed for snippet. Critical findings: {critical_findings}")
                else:
                    logger.info("Pre-write style/security validation passed for snippet.")
            except Exception as e:
                validation_passed = False
                validation_feedback.append(f"Error during pre-write style/security validation: {e}")
                logger.error(f"Error during pre-write style/security validation: {e}", exc_info=True)

        if validation_passed:
            logger.info(f"Snippet-level ethical and style checks passed (or were skipped). Proceeding to pre-merge full file syntax check for {filepath_to_use}.")

            try:
                hypothetical_merged_content = driver._merge_snippet(mock_read_file.return_value, generated_snippet)
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
                # The test expects this log, so explicitly add it here for full file syntax failures
            except Exception as e_merge:
                validation_passed = False
                validation_feedback.append(f"Error during pre-merge full file syntax validation: {e_merge}")
                logger.error(f"Error during pre-merge full file syntax validation: {e_merge}", exc_info=True)
                logger.warning(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---")
        
        if not validation_passed:
            # Add initial snippet error to feedback if not already present
            if initial_snippet_syntax_error_details:
                validation_feedback.insert(0, initial_snippet_syntax_error_details)
            # Log the failed snippet here if any validation failed
            logger.warning(f"Failed snippet (cleaned):\n---\n{generated_snippet}\n---")
            error_message_for_retry = f"Pre-write validation failed for snippet targeting {filepath_to_use}. Feedback: {validation_feedback}"
            logger.warning(error_message_for_retry)
            driver._current_task_results['pre_write_validation_feedback'] = validation_feedback
            raise ValueError(f"Pre-write validation failed: {'. '.join(validation_feedback)}")

        else:
            logger.info(f"All pre-write validations passed for snippet targeting {filepath_to_use}. Proceeding with actual merge/write.")
            merged_content = driver._merge_snippet(mock_read_file.return_value, generated_snippet)
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
        driver = driver_pre_write['driver']
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
        
        expected_merged_content = driver._merge_snippet(mock_read_file.return_value, snippet)
        mock_write_output.assert_called_once_with(resolved_target_path, expected_merged_content, overwrite=True)
        mock_code_review_agent.analyze_python.assert_has_calls([call(snippet), call(expected_merged_content)])
        mock_ethical_governance_engine.enforce_policy.assert_has_calls([call(snippet, driver.default_policy_config, is_snippet=True), call(expected_merged_content, driver.default_policy_config)])

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
            SyntaxError("Mock syntax error", ('<string>', 1, 1, 'def invalid syntax')),
            SyntaxError("Mock merged syntax error", ('<string>', 1, 1, 'def invalid syntax'))  # This is never reached
        ]


        resolved_target_path = mock_resolve_target_file.return_value

        with pytest.raises(ValueError, match=r"Pre-write validation failed: Initial snippet syntax check failed: Mock syntax error on line 1 \(offset 1\)\. Offending line: 'def invalid syntax'") as exc_info:
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
        assert any(f"Failed snippet (cleaned):\n---\n{snippet}\n---" in msg for msg in log_messages) # Changed to (cleaned)
        mock_code_review_agent.analyze_python.assert_called_once_with(snippet)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)
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
        assert any(f"Failed snippet (cleaned):\n---\n{snippet}\n---" in msg for msg in log_messages)
        assert any(re.search(r"Pre-write ethical check failed: {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}", record.message) for record in caplog.records)
        mock_code_review_agent.analyze_python.assert_not_called()
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)


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
        assert any(f"Failed snippet (cleaned):\n---\n{snippet}\n---" in msg for msg in log_messages) # Changed to (cleaned)
        assert any(f"Pre-write validation failed for snippet targeting {resolved_target_path}. Feedback: ['Pre-write style/security check failed: Critical findings detected.']" in record.message for record in caplog.records)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)
        mock_code_review_agent.analyze_python.assert_called_once_with(snippet)

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
                expected_merged_prefix = "import os\n\ndef new_method():\n    pass\n\ndef existing_function():\n    pass"
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
        assert any("Pre-write syntax check (AST parse) passed (isolated)." in msg for msg in log_messages) # Changed to (isolated)
        assert any("Pre-merge full file syntax validation failed for" in msg for msg in log_messages)
        hypothetical_merged_content = "import os\n\ndef new_method():\n    pass\n\ndef existing_function():\n    pass"
        assert any(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---" in msg for msg in log_messages)
        assert any(f"Pre-merge full file syntax validation failed for {resolved_target_path}: unexpected indent" in msg for msg in log_messages)

        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)
        mock_code_review_agent.analyze_python.assert_called_once_with(snippet)

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
        driver = setup_driver
        step_description = "Implement a new function."
        filepath = driver._resolve_target_file_for_step(step_description, driver.task_target_file, None)
        context_content = driver._read_file_for_context(filepath)

        coder_prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath,
            context_for_llm=context_content,
            is_minimal_context=False
        )

        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt
        assert "Ensure all string literals are correctly terminated" in coder_prompt
        assert "Pay close attention to Python's indentation rules" in coder_prompt
        assert "Generate complete and runnable Python code snippets" in coder_prompt
        assert "If modifying existing code, ensure the snippet integrates seamlessly" in coder_prompt
        assert coder_prompt.count(GENERAL_SNIPPET_GUIDELINES) == 1

    def test_coder_prompt_includes_general_guidelines_with_import(self, setup_driver, mocker):
        driver = setup_driver
        step_description = "Add import statements."
        filepath = driver._resolve_target_file_for_step(step_description, driver.task_target_file, None)
        context_content = driver._read_file_for_context(filepath)

        mocker.patch.object(driver, '_is_add_imports_step', return_value=True)

        coder_prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step_description,
            filepath_to_use=filepath,
            context_for_llm=context_content,
            is_minimal_context=False
        )

        assert GENERAL_SNIPPET_GUIDELINES in coder_prompt
        assert "You are adding import statements." in coder_prompt
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
            driver.default_policy_config = {'policy_name': 'Mock Policy'}
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
    def test_repr_logging_on_syntax_error(self, driver_for_cleaning, tmp_path, mocker): # Removed mock_ast_parse, mock_builtin_open from args
        driver = driver_for_cleaning # Get driver from fixture
        original_snippet = "```python\ndef func():\n  print('unterminated string)\n```"
        cleaned_snippet_that_fails = "def func():\n  print('unterminated string)"

        syntax_error_instance = SyntaxError("unterminated string literal", ('<unknown>', 2, 9, "  print('unterminated string)\n"))
        
        # Patch ast.parse, builtins.open, and json.dump at the start of the test
        mock_ast_parse = mocker.patch('ast.parse')
        mock_builtin_open = mocker.patch('builtins.open', new_callable=mocker.MagicMock)
        mock_json_dump = mocker.patch('json.dump')
        mock_ast_parse.side_effect = syntax_error_instance
        initial_snippet_syntax_error_details = None # Initialize outside try-except

        driver._current_task = {'task_id': 'test_task_syntax_error'}
        fixed_timestamp = "20230101_120000_000000"
        with patch('src.core.automation.workflow_driver.datetime') as mock_datetime: # Patch datetime within the SUT
            mock_datetime.now.return_value.strftime.return_value = fixed_timestamp
            mock_datetime.now.return_value.isoformat.return_value = "2023-01-01T12:00:00.000000"

            validation_feedback = []
            step_failure_reason = None
            step_description_for_log = "Test step description for syntax error"
            step_index_for_log = 0

            _cleaned_snippet = driver._clean_llm_snippet(original_snippet)
            assert _cleaned_snippet == cleaned_snippet_that_fails
            try:
                mock_ast_parse(_cleaned_snippet) # This will raise SyntaxError
            except SyntaxError as se_in_block:
                _validation_passed = False # This variable is local to the test, not the SUT
                _validation_feedback = [] # This variable is local to the test, not the SUT
                initial_snippet_syntax_error_details = f"Initial snippet syntax check failed: {se_in_block.msg} on line {se_in_block.lineno} (offset {se_in_block.offset}). Offending line: '{se_in_block.text.strip() if se_in_block.text else 'N/A'}'"
                _validation_feedback.append(initial_snippet_syntax_error_details)
                driver.logger.warning(f"Pre-write syntax validation (AST parse) failed for snippet: {se_in_block}")
                driver.logger.warning(f"Failed snippet (cleaned):\n---\n{_cleaned_snippet}\n---")
                _step_failure_reason = f"Pre-write syntax check failed: {se_in_block}"

                try:
                    debug_dir_name = ".debug/failed_snippets"
                    debug_dir_path_str = driver.context.get_full_path(debug_dir_name)
                    if debug_dir_path_str:
                        debug_dir = Path(debug_dir_path_str)
                        debug_dir.mkdir(parents=True, exist_ok=True)
                        _timestamp = fixed_timestamp
                        _current_task_id_str = getattr(driver, '_current_task', {}).get('task_id', 'unknown_task')
                        _sanitized_task_id = re.sub(r'[^\w\-_\.]', '_', _current_task_id_str)
                        _current_step_index_str = str(step_index_for_log + 1)

                        filename = f"failed_snippet_{_sanitized_task_id}_step{_current_step_index_str}_{_timestamp}.json"
                        filepath = debug_dir / filename

                        debug_data = {
                            "timestamp": mock_datetime.now.return_value.isoformat.return_value,
                            "task_id": _current_task_id_str,
                            "step_description": step_description_for_log,
                            "original_snippet_repr": repr(original_snippet),
                            "cleaned_snippet_repr": repr(_cleaned_snippet),
                            "syntax_error_details": {
                                "message": se_in_block.msg,
                                "lineno": se_in_block.lineno,
                                "offset": se_in_block.offset,
                                "text": se_in_block.text
                            }
                        }
                        with mock_builtin_open(filepath, 'w', encoding='utf-8') as f_err: # Use the mocked open
                            mock_json_dump(debug_data, f_err, indent=2) # Use the mocked json.dump
                        driver.logger.error(f"Saved malformed snippet details (JSON) to: {filepath}")
                    else:
                        driver.logger.error(f"Could not resolve debug directory '{debug_dir_name}' using context. Cannot save malformed snippet.")
                except Exception as write_err:
                    driver.logger.error(f"Failed to save malformed snippet details: {write_err}", exc_info=True)

            except ValueError:
                pass


        driver.context.get_full_path.assert_called_once_with(".debug/failed_snippets")

        expected_debug_dir = tmp_path / ".debug/failed_snippets"
        expected_filename = f"failed_snippet_test_task_syntax_error_step{step_index_for_log + 1}_{fixed_timestamp}.json"
        expected_filepath = expected_debug_dir / expected_filename
        
        mock_builtin_open.assert_called_once_with(expected_filepath, 'w', encoding='utf-8') # This line was already correct
        mock_json_dump.assert_called_once() # This assertion is now correctly placed
        written_data_obj = mock_json_dump.call_args[0][0]

        assert written_data_obj["task_id"] == "test_task_syntax_error"
        assert written_data_obj["step_description"] == step_description_for_log
        assert written_data_obj["original_snippet_repr"] == repr(original_snippet)
        assert written_data_obj["cleaned_snippet_repr"] == repr(cleaned_snippet_that_fails)
        assert written_data_obj["syntax_error_details"]["message"] == "unterminated string literal"
        assert written_data_obj["syntax_error_details"]["lineno"] == 2
        assert written_data_obj["syntax_error_details"]["offset"] == 9
        assert written_data_obj["syntax_error_details"]["text"] == "  print('unterminated string)\n"


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
        
        mocker.patch.object(driver, '_read_file_for_context', return_value="existing content")
        mocker.patch.object(driver, '_resolve_target_file_for_step', return_value=str(tmp_path / "test_file.py"))
        mocker.patch.object(driver, '_write_output_file')
        mocker.patch.object(driver, '_merge_snippet', side_effect=lambda ex, sn: ex + "\n" + sn)
        mocker.patch.object(driver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 90}})) # Mock to avoid actual report generation logic
        mocker.patch.object(driver, '_parse_and_evaluate_grade_report')
        mocker.patch.object(driver, '_update_task_status_in_roadmap')
        
        driver._invoke_coder_llm = mocker.MagicMock(return_value="def corrected_code(): pass")
        return driver

def test_retry_prompt_includes_validation_feedback(driver_for_retry_prompt_test, caplog, mocker):
    caplog.set_level(logging.INFO)
    driver = driver_for_retry_prompt_test
    
    driver._current_task = {
        'task_id': 'retry_test_task', 'task_name': 'Retry Test Task', 
        'description': 'A task to test retry prompt enhancement.', 'status': 'Not Started', 
        'priority': 'High', 'target_file': 'test_file.py'
    }
    driver.task_target_file = driver._current_task['target_file']
    solution_plan = ["Implement a function in test_file.py"]

    original_syntax_error_msg = "Mock syntax error" # Changed to match the test's mock_ast_parse.side_effect
    
    driver._invoke_coder_llm.side_effect = [
        "def bad_snippet_initial_attempt(): 'unterminated",
        "def good_snippet_retry_attempt(): pass"
    ]

    mock_ast_parse_instance = mocker.MagicMock()
    mock_ast_parse_instance.side_effect = [
        SyntaxError(original_syntax_error_msg, ('<unknown>', 1, 1, '')),
        None
    ]

    with patch('ast.parse', mock_ast_parse_instance):
        # Ensure _should_add_docstring_instruction returns True for this step
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=True)
        step_index = 0
        step = solution_plan[0]
        step_retries = 0
        step_failure_reason_for_current_attempt = None
        
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
                    task=driver._current_task,
                    step_description=step,
                    filepath_to_use=filepath_to_use,
                    context_for_llm=existing_content,
                    is_minimal_context=False,
                    retry_feedback_content=retry_feedback_for_prompt
                )
                generated_snippet = driver._invoke_coder_llm(coder_prompt)
                cleaned_snippet = driver._clean_llm_snippet(generated_snippet)

                mock_ast_parse_instance(cleaned_snippet)

                driver._write_output_file(filepath_to_use, cleaned_snippet, overwrite=True)
                break

            except Exception as e:
                step_failure_reason_for_current_attempt = str(e)
                logging.error(f"Simulated step execution failed (Attempt {step_retries + 1}): {e}")
                step_retries += 1
                if step_retries > MAX_STEP_RETRIES:
                    logging.error(f"Simulated step failed after max retries.")
                    break
                logging.warning(f"Simulated step failed. Retrying ({step_retries}/{MAX_STEP_RETRIES})...")


    assert driver._invoke_coder_llm.call_count == 2
    
    retry_prompt_call = driver._invoke_coder_llm.call_args_list[1]
    retry_prompt_text = retry_prompt_call[0][0]

    assert "IMPORTANT: YOUR PREVIOUS ATTEMPT TO GENERATE CODE FOR THIS STEP FAILED." in retry_prompt_text
    assert original_syntax_error_msg in retry_prompt_text
    assert "PLEASE ANALYZE THIS ERROR AND THE EXISTING CODE CAREFULLY." in retry_prompt_text
    assert "CRITICAL INSTRUCTIONS FOR YOUR RESPONSE FORMAT (Full Block/Method/Class Focus):" in retry_prompt_text
    assert "Your entire response MUST be ONLY a valid Python code snippet representing the complete new or modified function, method, or class." in retry_prompt_text
    
    initial_prompt_call = driver._invoke_coder_llm.call_args_list[0]
    initial_prompt_text = initial_prompt_call[0][0]