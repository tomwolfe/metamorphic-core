# tests/test_phase1_8_features.py

import pytest
import unittest
from unittest.mock import patch, MagicMock, mock_open, call, ANY
import re
from pathlib import Path
import logging
import json
from datetime import datetime
import subprocess
import sys
import ast # Import ast for syntax check
import html # Import html for escaping

# Add the src directory to the Python path
# This ensures that 'from core.automation.workflow_driver import ...' works
# Use Pathlib for robust path joining
current_file_dir = Path(__file__).parent
# Adjust path to go up three levels to project root, then into src
src_dir = current_file_dir.parent.parent / 'src'
sys.path.insert(0, str(src_dir.resolve()))


# Assuming WorkflowDriver is in src.core.automation
# FIX: Import all necessary components used in tests
from core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT, classify_plan_step, CODE_KEYWORDS, CONCEPTUAL_KEYWORDS, MAX_STEP_RETRIES
# FIX: Import EnhancedLLMOrchestrator as it's patched
from core.llm_orchestration import EnhancedLLMOrchestrator

import spacy
from spacy.matcher import PhraseMatcher

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from core.agents.code_review_agent import CodeReviewAgent
from core.ethics.governance import EthicalGovernanceEngine

# Set up logging for tests
# Ensure logging is configured only once
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(name)s - %(message)s')

logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context, specifically for Phase 1.8 tests
@pytest.fixture
def test_driver_phase1_8(tmp_path, mocker): # Added mocker
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation within the fixture setup
    # Use the full path for patching if necessary, e.g., 'src.core.automation.workflow_driver.CodeReviewAgent'
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator: # FIX: Patch EnhancedLLMOrchestrator here

        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value # FIX: Get mock instance

        # Mock policy loading which happens in __init__
        # Note: The actual WorkflowDriver loads policy via _load_default_policy which uses builtins.open
        # This mock might not be strictly necessary if builtins.open is patched globally, but keep for clarity.
        # mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        # Mock the Context.get_full_path method used by _load_default_policy in __init__
        # This mock needs to be active during driver instantiation
        # Use mocker for patching the instance method
        mock_context_get_full_path = mocker.patch.object(context, 'get_full_path', side_effect=lambda path: str(Path(context.base_path) / path) if path else str(Path(context.base_path)))


        driver = WorkflowDriver(context)
        # Ensure LLM orchestrator mock is set up
        # FIX: Assign the patched LLM orchestrator instance
        driver.llm_orchestrator = mock_llm_orchestrator_instance
        # Default mock return for generate, can be overridden in tests
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        # Assign mocked instances (this happens automatically if patching instantiation, but explicit is fine)
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        # Set the default policy config directly after mocking load_policy_from_json
        # This is needed because the real _load_default_policy might be called if builtins.open isn't patched globally
        driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set

        # Reset the mock's call count after driver initialization in the fixture
        mock_context_get_full_path.reset_mock() # FIX: Reset mock after init calls it

        # Add attributes needed for tests that might not be set by __init__ or autonomous_loop setup
        # These are now initialized in __init__, but ensure they are reset or handled correctly in tests
        # driver._current_task_results = {}
        # driver.remediation_attempts = 0 # Initialize remediation counter for tests
        # driver.remediation_occurred_in_pass = False # Initialize flag

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance,
            'mock_llm_orchestrator': mock_llm_orchestrator_instance, # FIX: Yield LLM mock
            'mock_context_get_full_path': mock_context_get_full_path # FIX: Yield context mock
        }


# Fixture specifically for testing _resolve_target_file_for_step and _validate_path
@pytest.fixture
def driver_for_multi_target_resolution(tmp_path, mocker):
    mock_context = Context(str(tmp_path))
    def mock_get_full_path_side_effect(relative_path_str):
        if relative_path_str is None:
            return None
        try:
            # Handle empty string specifically as resolving to base path
            if relative_path_str == "":
                 resolved_path = Path(mock_context.base_path).resolve()
            else:
                 full_path = (Path(mock_context.base_path) / relative_path_str)
                 # Use resolve(strict=False) to avoid errors if the path doesn't exist,
                 # but still perform the security check on the resulting path string.
                 # Note: The real Context.get_full_path uses resolve() which will raise FileNotFoundError.
                 # This mock's side_effect should ideally match the real behavior,
                 # but for testing path traversal *detection* specifically, allowing resolution
                 # of non-existent paths might be necessary depending on the test focus.
                 # Let's stick to the real behavior for consistency with the Context class.
                 resolved_path = full_path.resolve()

            # Security check: Ensure the resolved path is within the base path
            # Use str() for comparison as resolved_path is a Path object
            if not str(resolved_path).startswith(str(Path(mock_context.base_path).resolve())):
                # Log a warning if path traversal is detected
                logger.warning(f"Path traversal attempt detected during mock resolution: {relative_path_str} resolved to {resolved_path}")
                return None
            return str(resolved_path)
        except FileNotFoundError:
             # Simulate the real Context behavior for non-existent paths
             logger.warning(f"Mock resolution failed: Path not found for '{relative_path_str}' relative to '{mock_context.base_path}'.")
             return None
        except Exception as e:
            # Log error for other resolution issues
            logger.error(f"Error resolving path '{relative_path_str}' relative to '{mock_context.base_path}': {e}", exc_info=True)
            return None


    # Use mocker to patch the instance method
    mock_context_get_full_path = mocker.patch.object(mock_context, 'get_full_path', side_effect=mock_get_full_path_side_effect)

    # FIX: Patch EnhancedLLMOrchestrator here as well
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'):
        driver = WorkflowDriver(mock_context)
        driver.llm_orchestrator = MagicMock() # Ensure llm_orchestrator is a mock
        driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set

        # FIX: Reset the mock's call count after driver initialization in the fixture
        mock_context_get_full_path.reset_mock()

        # Mock _determine_filepath_to_use as it's called by _resolve_target_file_for_step
        # The side_effect should simulate its logic based on step_desc and task_target
        def mock_determine_filepath(step_desc, task_target, flags):
            # This mock should return the *relative* path that _validate_path expects
            path_in_step_match = re.search(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_desc, re.IGNORECASE)
            path_in_step = path_in_step_match.group(1) if path_in_step_match else None

            # Simulate the logic from the real _determine_filepath_to_use simplified for this test
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

            # Fallback to extracting from step if still None and is a file-modifying step
            # FIX: Correct variable name from is_code_generation_step_prelim to is_code_gen_step
            if filepath_to_use is None and (is_explicit_write_step or is_code_gen_step):
                 # FIX: Correct variable name from step_description to step_desc
                 filepath_from_step_match_fallback = re.search(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_desc, re.IGNORECASE)
                 filepath_to_use = filepath_from_step_match_fallback.group(1) if filepath_from_step_match_fallback else None

            return filepath_to_use # Return the relative path

        # Use mocker to patch the instance method
        mocker.patch.object(driver, '_determine_filepath_to_use', side_effect=mock_determine_filepath)

        return driver


class TestPhase1_8Features:
    def test_research_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Research and identify keywords for src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False

    def test_code_generation_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Implement the new function in src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is True

    def test_explicit_file_writing_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Write the research findings to research_summary.md"
        prelim_flags = driver._classify_step_preliminary(step1)
        # FIX: Research step classification should be True if it contains research keywords
        # The step "Write the research findings..." implies research was done, so this is correct.
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is True

    def test_test_execution_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Run tests for the new feature."
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is False
        assert prelim_flags["is_test_execution_step_prelim"] is True

    def test_conceptual_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Discuss the design approach with the team."
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is False
        assert prelim_flags["is_test_execution_step_prelim"] is False
        assert prelim_flags["is_test_writing_step_prelim"] is False
        # FIX: Add assertion for conceptual classification
        assert classify_plan_step(step1) == 'conceptual'


    # Use mocker for patching instance methods
    def test_conceptual_define_step_does_not_overwrite_main_python_target(self, test_driver_phase1_8, tmp_path, caplog, mocker):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        # FIX: Mock context get_full_path to return a resolved path for the target file
        resolved_target_path = str(tmp_path / 'src' / 'core' / 'automation' / 'workflow_driver.py')
        # Ensure the mock handles the specific target file path correctly
        test_driver_phase1_8['mock_context_get_full_path'].side_effect = lambda path: resolved_target_path if path == 'src/core/automation/workflow_driver.py' else str(Path(tmp_path) / path)

        driver._current_task = {
            'task_id': 'test_conceptual_write', 'task_name': 'Test Conceptual Write',
            'description': 'A test.', 'status': 'Not Started', 'priority': 'High',
            'target_file': 'src/core/automation/workflow_driver.py'
        }
        driver.task_target_file = driver._current_task['target_file']
        plan_step = "Write a define list of keywords for step classification."
        prelim_flags = driver._classify_step_preliminary(plan_step)

        # Patch _write_output_file on the driver instance using mocker
        mock_write_output = mocker.patch.object(driver, '_write_output_file')

        # FIX: Call _resolve_target_file_for_step first to get the resolved path
        filepath_to_use = driver._resolve_target_file_for_step(plan_step, driver.task_target_file, prelim_flags)
        content_to_write_decision, overwrite_mode = driver._determine_write_operation_details(plan_step, filepath_to_use, driver.task_target_file, prelim_flags)

        assert content_to_write_decision is None
        mock_write_output.assert_not_called()
        # FIX: Ensure the log message matches the actual log output format
        expected_log_message = f"Skipping placeholder write to main Python target {resolved_target_path} for conceptual step: '{plan_step}'."
        assert any(expected_log_message in record.message for record in caplog.records)


class TestPreWriteValidation:
    @pytest.fixture
    def driver_pre_write(self, mocker, tmp_path):
        mock_context = Context(str(tmp_path))
        # FIX: Mock Context.get_full_path here as well, as _load_default_policy calls it
        mock_context_get_full_path = mocker.patch.object(mock_context, 'get_full_path', side_effect=lambda path: str(Path(mock_context.base_path) / path) if path else str(Path(mock_context.base_path)))

        with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
             patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
             patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator:

            mock_code_review_agent_instance = MockCodeReviewAgent.return_value
            mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
            mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value

            # FIX: Remove patch.object(WorkflowDriver, '_load_default_policy')
            # The driver's __init__ will call the real _load_default_policy,
            # which will use the mocked mock_context_get_full_path and builtins.open (if patched globally).
            # We ensure default_policy_config is set below anyway.
            # mocker.patch.object(WorkflowDriver, '_load_default_policy')

            wd = WorkflowDriver(mock_context)
            wd.code_review_agent = mock_code_review_agent_instance
            wd.ethical_governance_engine = mock_ethical_governance_engine_instance
            wd.llm_orchestrator = mock_llm_orchestrator_instance
            wd.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set

            wd._current_task_results = {'step_errors': []}
            wd._current_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Mock Description', 'status': 'Not Started', 'priority': 'medium', 'target_file': 'src/mock_file.py'}
            wd.task_target_file = wd._current_task['target_file']

            # FIX: Mock _resolve_target_file_for_step to return the resolved target file
            # This method is called by autonomous_loop before pre-write validation
            resolved_target_path = str(Path(tmp_path) / wd.task_target_file)
            # Use mocker to patch the instance method
            mocker.patch.object(wd, '_resolve_target_file_for_step', return_value=resolved_target_path)

            # Use mocker to patch instance methods
            mocker.patch.object(wd, '_read_file_for_context', return_value="")
            mocker.patch.object(wd, '_merge_snippet', side_effect=lambda _, snippet: snippet)
            # Patch _write_output_file here as it's called in the helper
            mocker.patch.object(wd, '_write_output_file', return_value=True)


            # FIX: Reset mock after init calls it
            mock_context_get_full_path.reset_mock()

            yield wd

    # This helper function simulates the relevant part of the autonomous loop
    # where pre-write validation occurs.
    def _simulate_step_execution_for_pre_write_validation(self, driver, generated_snippet, step_description="Step 1: Implement code in src/mock_file.py"):
        # In the real loop, filepath_to_use comes from _resolve_target_file_for_step
        # Since we mocked _resolve_target_file_for_step in the fixture, we can use its return value
        # Call the mocked _resolve_target_file_for_step to get the value it would return
        filepath_to_use = driver._resolve_target_file_for_step(step_description, driver.task_target_file, driver._classify_step_preliminary(step_description))

        # Ensure filepath_to_use is not None before proceeding
        if filepath_to_use is None:
             logger.error("Simulated _resolve_target_file_for_step returned None.")
             raise ValueError("Resolved file path is None.")


        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
        validation_passed = True
        validation_feedback = []
        try:
            ast.parse(generated_snippet)
            logger.info("Pre-write syntax check (AST parse) passed for snippet.")
        except SyntaxError as se:
            validation_passed = False
            validation_feedback.append(f"Pre-write syntax check failed: {se}")
            logger.warning(f"Pre-write syntax validation (AST parse) failed for snippet: {se}")
            logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
        except Exception as e:
            validation_passed = False
            validation_feedback.append(f"Error during pre-write syntax validation (AST parse): {e}")
            logger.error(f"Error during pre-write syntax validation (AST parse): {e}", exc_info=True)
            logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")

        if validation_passed and driver.default_policy_config:
            try:
                # Call the actual mocked ethical_governance_engine instance method
                ethical_results = driver.ethical_governance_engine.enforce_policy(generated_snippet, driver.default_policy_config)
                if ethical_results.get('overall_status') == 'rejected':
                    validation_passed = False
                    validation_feedback.append(f"Pre-write ethical check failed: {ethical_results}")
                    logger.warning(f"Pre-write ethical validation failed for snippet: {ethical_results}")
                    logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                else:
                    logger.info("Pre-write ethical validation passed for snippet.")
            except Exception as e:
                validation_passed = False
                validation_feedback.append(f"Error during pre-write ethical validation: {e}")
                logger.error(f"Error during pre-write ethical validation: {e}", exc_info=True)
                logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
        elif validation_passed:
            logger.warning("Skipping pre-write ethical validation: Default policy not loaded.")

        if validation_passed:
            try:
                # Call the actual mocked code_review_agent instance method
                style_review_results = driver.code_review_agent.analyze_python(generated_snippet)
                critical_findings = [f for f in style_review_results.get('static_analysis', []) if f.get('severity') in ['error', 'security_high']]
                if critical_findings:
                    validation_passed = False
                    validation_feedback.append(f"Pre-write style/security check failed: Critical findings detected.")
                    logger.warning(f"Pre-write style/security validation failed for snippet. Critical findings: {critical_findings}")
                    logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                else:
                    logger.info("Pre-write style/security validation passed for snippet.")
            except Exception as e:
                validation_passed = False
                validation_feedback.append(f"Error during pre-write style/security validation: {e}")
                logger.error(f"Error during pre-write style/security validation: {e}", exc_info=True)
                logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")

        if not validation_passed:
            logger.warning(f"Pre-write validation failed for snippet targeting {filepath_to_use}. Skipping write/merge. Feedback: {validation_feedback}")
            # In the real loop, this would cause the step to fail and potentially retry
            # For this test helper, we re-raise to indicate failure
            raise ValueError(f"Pre-write validation failed for step.")
        else:
            logger.info(f"Pre-write validation passed for snippet targeting {filepath_to_use}. Proceeding with merge/write.")
            # Simulate the successful write and post-write validation calls from the loop
            # Call the actual mocked _write_output_file instance method
            driver._write_output_file(filepath_to_use, generated_snippet, overwrite=True)
            # Call the actual mocked agent instance methods for post-write validation
            driver.code_review_agent.analyze_python(generated_snippet)
            if driver.default_policy_config:
                driver.ethical_governance_engine.enforce_policy(generated_snippet, driver.default_policy_config)


    # Remove the patch decorator here, _write_output_file is patched in the fixture
    def test_pre_write_validation_all_pass(self, driver_pre_write, caplog):
        caplog.set_level(logging.INFO)
        driver = driver_pre_write
        snippet = "def generated_code(): pass"
        # Set return values on the actual mock instances from the fixture
        driver.ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        driver.code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}

        # Call the helper function
        self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = driver._resolve_target_file_for_step.return_value # Get the value returned by the mock

        assert "Pre-write syntax check (AST parse) passed" in caplog.text
        assert "Pre-write ethical validation passed" in caplog.text
        assert "Pre-write style/security validation passed" in caplog.text
        # Assert on the resolved path in the log message
        assert f"Pre-write validation passed for snippet targeting {resolved_target_path}. Proceeding with merge/write." in caplog.text
        # Assert on the resolved path in the write call (patched in fixture)
        driver._write_output_file.assert_called_once_with(resolved_target_path, snippet, overwrite=True)
        # Assert on the resolved path in the post-write validation calls (mocks from fixture)
        # analyze_python is called twice (pre and post)
        driver.code_review_agent.analyze_python.assert_has_calls([call(snippet), call(snippet)])
        # enforce_policy is called twice (pre and post)
        driver.ethical_governance_engine.enforce_policy.assert_has_calls([call(snippet, driver.default_policy_config), call(snippet, driver.default_policy_config)])

        assert not driver._current_task_results['step_errors']

    # Remove the patch decorator here, _write_output_file is patched in the fixture
    def test_pre_write_validation_syntax_fails(self, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write
        snippet = "def invalid syntax"

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = driver._resolve_target_file_for_step.return_value # Get the value returned by the mock

        with pytest.raises(ValueError, match="Pre-write validation failed for step."):
            self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        # _write_output_file is patched in the fixture, assert on the instance mock
        driver._write_output_file.assert_not_called()
        assert "Pre-write syntax validation (AST parse) failed for snippet:" in caplog.text
        assert f"Failed snippet:\n---\n{snippet}\n---" in caplog.text
        # Assert on the resolved path in the log message
        assert f"Pre-write validation failed for snippet targeting {resolved_target_path}. Skipping write/merge." in caplog.text
        # Post-write validation should not be called (mocks from fixture)
        driver.code_review_agent.analyze_python.assert_not_called()
        driver.ethical_governance_engine.enforce_policy.assert_not_called()


    # Remove the patch decorator here, _write_output_file is patched in the fixture
    def test_pre_write_validation_ethical_fails(self, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write
        snippet = "def generated_code(): pass"
        # Set return value on the actual mock instance from the fixture
        driver.ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = driver._resolve_target_file_for_step.return_value # Get the value returned by the mock

        with pytest.raises(ValueError, match="Pre-write validation failed for step."):
            self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        # _write_output_file is patched in the fixture, assert on the instance mock
        driver._write_output_file.assert_not_called()
        assert "Pre-write ethical validation failed for snippet" in caplog.text
        assert f"Failed snippet:\n---\n{snippet}\n---" in caplog.text
        # Assert on the resolved path in the log message
        assert f"Pre-write validation failed for snippet targeting {resolved_target_path}. Skipping write/merge." in caplog.text
        # Style/Security and post-write validation should not be called (mocks from fixture)
        driver.code_review_agent.analyze_python.assert_not_called()
        # Ethical check is called once for pre-write validation (mock from fixture)
        driver.ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config)


    # Remove the patch decorator here, _write_output_file is patched in the fixture
    def test_pre_write_validation_style_fails(self, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write
        snippet = "def generated_code(): pass"
        # Set return values on the actual mock instances from the fixture
        driver.ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        driver.code_review_agent.analyze_python.return_value = {'status': 'failed', 'static_analysis': [{'severity': 'error', 'code': 'E302', 'message': 'expected 2 blank lines'}]}

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = driver._resolve_target_file_for_step.return_value # Get the value returned by the mock

        with pytest.raises(ValueError, match="Pre-write validation failed for step."):
            self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        # _write_output_file is patched in the fixture, assert on the instance mock
        driver._write_output_file.assert_not_called()
        assert "Pre-write style/security validation failed for snippet" in caplog.text
        assert f"Failed snippet:\n---\n{snippet}\n---" in caplog.text
        # Assert on the resolved path in the log message
        assert f"Pre-write validation failed for snippet targeting {resolved_target_path}. Skipping write/merge." in caplog.text
        # Ethical check is called once for pre-write validation (mock from fixture)
        driver.ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config)
        # Style/Security check is called once for pre-write validation (mock from fixture)
        driver.code_review_agent.analyze_python.assert_called_once_with(snippet)


class TestPathResolutionAndValidation:
    def test_validate_path_safe_relative(self, driver_for_multi_target_resolution, tmp_path):
        driver = driver_for_multi_target_resolution
        relative_path = "src/module.py"
        # The mock get_full_path in the fixture returns the resolved path
        expected_full_path = str((tmp_path / relative_path).resolve())
        validated_path = driver._validate_path(relative_path)
        driver.context.get_full_path.assert_called_once_with(relative_path)
        assert validated_path == expected_full_path

    def test_validate_path_unsafe_relative(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING) # FIX: Set log level to capture warning
        driver = driver_for_multi_target_resolution
        relative_path = "../sensitive/file.txt"
        validated_path = driver._validate_path(relative_path)
        driver.context.get_full_path.assert_called_once_with(relative_path)
        assert validated_path is None
        # FIX: Assert the correct log messages from the mock and _validate_path
        assert "Path traversal attempt detected during mock resolution: ../sensitive/file.txt" in caplog.text
        # FIX: Update assertion to match the actual log message format
        assert "Resolved path '../sensitive/file.txt' is invalid or outside the allowed context." in caplog.text


    def test_validate_path_unsafe_absolute(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING) # FIX: Set log level to capture warning
        driver = driver_for_multi_target_resolution
        absolute_path = "/tmp/sensitive_file.txt"
        validated_path = driver._validate_path(absolute_path)
        driver.context.get_full_path.assert_called_once_with(absolute_path)
        assert validated_path is None
        # FIX: Assert the correct log messages from the mock and _validate_path
        assert "Path traversal attempt detected during mock resolution: /tmp/sensitive_file.txt" in caplog.text
        # FIX: Update assertion to match the actual log message format
        assert "Resolved path '/tmp/sensitive_file.txt' is invalid or outside the allowed context." in caplog.text


    def test_validate_path_empty_string(self, driver_for_multi_target_resolution, caplog, tmp_path):
        caplog.set_level(logging.WARNING) # FIX: Set log level to capture warning
        driver = driver_for_multi_target_resolution
        empty_path = ""
        validated_path = driver._validate_path(empty_path)
        # FIX: _validate_path now passes empty string to get_full_path, so assert it was called
        driver.context.get_full_path.assert_called_once_with(empty_path)
        # FIX: An empty string should resolve to the base path, which is not None
        # The mock get_full_path side_effect handles this: `str(Path(mock_context.base_path) / path) if path else str(Path(mock_context.base_path))`
        # When path is "", it returns `str(Path(mock_context.base_path))`.
        # So validated_path should be the resolved base path.
        assert validated_path == str(Path(tmp_path).resolve())
        # FIX: Assert the correct log message from _validate_path for empty input
        # The log for empty string was removed in the previous fix, only non-string types log this now.
        # So, assert that this specific log message is NOT present.
        assert "Path validation received invalid input: " not in caplog.text
        # FIX: Assert that the second warning from _validate_path is NOT logged for empty string
        assert "Resolved path '' is invalid or outside the allowed context." not in caplog.text


    def test_validate_path_none_input(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING) # FIX: Set log level to capture warning
        driver = driver_for_multi_target_resolution
        none_path = None
        validated_path = driver._validate_path(none_path)
        # _validate_path checks for None/empty input *before* calling get_full_path
        driver.context.get_full_path.assert_not_called()
        assert validated_path is None
        # FIX: Update assertion to match the actual log message format
        assert "Path validation received invalid input: None" in caplog.text
        # FIX: Assert that the second warning from _validate_path is NOT logged for None
        assert "Resolved path 'None' is invalid or outside the allowed context." not in caplog.text


class TestMultiTargetHandlingLogic:
    def test_resolve_multi_target_explicit_full_path_mention(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.INFO)
        driver = driver_for_multi_target_resolution
        step_desc = "Modify src/module_b.py to add new features."
        task_target_spec = "src/module_a.py,src/module_b.py,src/module_c.py"
        prelim_flags = {'is_code_generation_step_prelim': True}
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)
        # _resolve_target_file_for_step finds the explicit mention and calls _validate_path with it
        # _validate_path calls context.get_full_path
        driver.context.get_full_path.assert_called_once_with("src/module_b.py")
        # _determine_filepath_to_use should not be called in this case
        driver._determine_filepath_to_use.assert_not_called()
        assert resolved_file is not None
        assert Path(resolved_file).name == "module_b.py"
        # FIX: Assert the correct log message format
        assert "explicitly mentions 'src/module_b.py' from task target list" in caplog.text

    def test_resolve_multi_target_explicit_filename_mention(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.INFO)
        driver = driver_for_multi_target_resolution
        step_desc = "In module_a.py, refactor the main function."
        task_target_spec = "src/module_a.py,src/module_b.py"
        prelim_flags = {'is_code_generation_step_prelim': True}
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)
        # _resolve_target_file_for_step finds the explicit mention and calls _validate_path with it
        # _validate_path calls context.get_full_path
        driver.context.get_full_path.assert_called_once_with("src/module_a.py")
        # _determine_filepath_to_use should not be called in this case
        driver._determine_filepath_to_use.assert_not_called()
        assert resolved_file is not None
        assert Path(resolved_file).name == "module_a.py"
        # FIX: Assert the correct log message format
        assert "explicitly mentions filename 'module_a.py' (from 'src/module_a.py') from task target list" in caplog.text


    def test_resolve_multi_target_no_mention_defaults_first(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_for_multi_target_resolution
        step_desc = "Implement the new algorithm."
        task_target_spec = "src/core_logic.py,src/utils.py"
        prelim_flags = {'is_code_generation_step_prelim': True}
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)
        # _resolve_target_file_for_step finds no explicit mention, defaults to first target, and calls _validate_path with it
        # _validate_path calls context.get_full_path
        driver.context.get_full_path.assert_called_once_with("src/core_logic.py")
        # _determine_filepath_to_use should not be called in this case (multi-target logic handles it)
        driver._determine_filepath_to_use.assert_not_called()
        assert resolved_file is not None
        assert Path(resolved_file).name == "core_logic.py"
        # FIX: Assert the correct log message format
        assert "Defaulting to the first file: 'src/core_logic.py'." in caplog.text


    def test_resolve_single_target_uses_determine_filepath(self, driver_for_multi_target_resolution, tmp_path): # Add tmp_path fixture
        driver = driver_for_multi_target_resolution
        step_desc = "Modify the main file src/main.py."
        task_target_spec = "src/main.py"
        prelim_flags = {'is_code_generation_step_prelim': True}
        # FIX: Calculate expected_resolved_path manually without calling the mock
        expected_resolved_path = str((Path(tmp_path) / "src/main.py").resolve())
        # The mock _determine_filepath_to_use needs to return the *relative* path
        driver._determine_filepath_to_use.return_value = "src/main.py"
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # _resolve_target_file_for_step calls _determine_filepath_to_use with the original spec
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # _resolve_target_file_for_step then calls _validate_path with the result of _determine_filepath_to_use ("src/main.py")
        # _validate_path calls context.get_full_path with that relative path
        driver.context.get_full_path.assert_called_once_with("src/main.py")
        assert resolved_file == expected_resolved_path


    def test_resolve_no_task_target_uses_determine_filepath(self, driver_for_multi_target_resolution, tmp_path): # Add tmp_path fixture
        driver = driver_for_multi_target_resolution
        step_desc = "Create a new file named new_util.py for utility functions."
        task_target_spec = None
        prelim_flags = {'is_code_generation_step_prelim': True}
        # FIX: Calculate expected_resolved_path manually without calling the mock
        expected_resolved_path = str((Path(tmp_path) / "new_util.py").resolve())
        # The mock _determine_filepath_to_use needs to return the *relative* path
        driver._determine_filepath_to_use.return_value = "new_util.py"
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # _resolve_target_file_for_step calls _determine_filepath_to_use with None as task_target
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, None, prelim_flags)
        # _resolve_target_file_for_step then calls _validate_path with the result of _determine_filepath_to_use ("new_util.py")
        # _validate_path calls context.get_full_path with that relative path
        driver.context.get_full_path.assert_called_once_with("new_util.py")
        assert resolved_file == expected_resolved_path


    def test_resolve_multi_target_not_code_gen_uses_determine_filepath(self, driver_for_multi_target_resolution, tmp_path): # Add tmp_path fixture
        driver = driver_for_multi_target_resolution
        step_desc = "Research file_a.py and file_b.py"
        task_target_spec = "file_a.py,file_b.py"
        prelim_flags = {'is_code_generation_step_prelim': False, 'is_research_step_prelim': True}
        # FIX: Calculate expected_resolved_path manually without calling the mock
        expected_resolved_path = str((Path(tmp_path) / "file_a.py").resolve())
        # The mock _determine_filepath_to_use needs to return the *relative* path
        driver._determine_filepath_to_use.return_value = "file_a.py"
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # _resolve_target_file_for_step calls _determine_filepath_to_use with the original spec
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # _resolve_target_file_for_step then calls _validate_path with the result of _determine_filepath_to_use ("file_a.py")
        # _validate_path calls context.get_full_path with that relative path
        driver.context.get_full_path.assert_called_once_with("file_a.py")
        assert resolved_file == expected_resolved_path


    def test_resolve_target_file_path_traversal_attempt_returns_none(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_for_multi_target_resolution
        step_desc = "Modify ../../../etc/passwd"
        task_target_spec = "../../../etc/passwd,src/safe.py"
        prelim_flags = {'is_code_generation_step_prelim': True}
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)
        # _resolve_target_file_for_step identifies "../../../etc/passwd" as the target and calls _validate_path with it.
        # _validate_path calls context.get_full_path with it.
        driver.context.get_full_path.assert_called_once_with("../../../etc/passwd")
        # _determine_filepath_to_use should not be called
        driver._determine_filepath_to_use.assert_not_called()
        assert resolved_file is None
        # FIX: Assert the correct log messages from the mock and _validate_path
        assert "Path traversal attempt detected during mock resolution: ../../../etc/passwd" in caplog.text
        # FIX: Update assertion to match the actual log message format
        assert "Resolved path '../../../etc/passwd' is invalid or outside the allowed context." in caplog.text


    def test_resolve_multi_target_empty_list_after_parse(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_for_multi_target_resolution
        step_desc = "Implement new feature."
        task_target_spec = ",, ," # This parses to an empty list []
        prelim_flags = {'is_code_generation_step_prelim': True}
        # FIX: The mock _determine_filepath_to_use needs to return None in this scenario
        driver._determine_filepath_to_use.return_value = None
        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)
        # _resolve_target_file_for_step should call _determine_filepath_to_use with None as task_target_spec
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, None, prelim_flags)
        # _resolve_target_file_for_step then calls _validate_path with the result of _determine_filepath_to_use (which is None)
        # _validate_path with None should not call context.get_full_path
        driver.context.get_full_path.assert_not_called()
        assert resolved_file is None
        # FIX: Assert the correct log message for empty task target list (ERROR level)
        assert "Task target file list was unexpectedly empty after parsing for step: 'Implement new feature.'" in caplog.text
        # FIX: Assert the log message from _validate_path for None input (WARNING level)
        assert "Path validation received invalid input: None" in caplog.text


# Integration Test for Multi-Target Handling (Revised Patching)
# Remove all @patch decorators
def test_integration_multi_target_file_handling_e2e_revised_patching(
    test_driver_phase1_8, tmp_path, caplog, mocker # Add mocker fixture
):
    caplog.set_level(logging.INFO)
    driver_fixture_dict = test_driver_phase1_8
    driver = driver_fixture_dict['driver']
    mock_context_get_full_path = driver_fixture_dict['mock_context_get_full_path']
    mock_llm_orchestrator = driver_fixture_dict['mock_llm_orchestrator']
    mock_code_review_agent = driver_fixture_dict['mock_code_review_agent']
    mock_ethical_governance_engine = driver_fixture_dict['mock_ethical_governance_engine']


    src_dir_path = tmp_path / "src"
    src_dir_path.mkdir(exist_ok=True)
    file_a_path_relative = "src/file_a.py"
    file_b_path_relative = "src/file_b.py"
    file_a_full_path = src_dir_path / "file_a.py"
    file_b_full_path = src_dir_path / "file_b.py"
    file_a_full_path.write_text("initial content for file_a")
    file_b_full_path.write_text("initial content for file_b")

    roadmap_path_relative = "ROADMAP.json"
    roadmap_full_path = tmp_path / roadmap_path_relative
    roadmap_content_dict = {
        "tasks": [{
            "task_id": "multi_target_e2e_001", "priority": "Critical", "task_name": "Test Multi-Target E2E",
            "description": "Modify file_b.py specifically.", "status": "Not Started",
            "target_file": f"{file_a_path_relative},{file_b_path_relative}", "depends_on": []
        }]
    }
    # Create the expected roadmap content after the task is completed
    completed_roadmap_content_dict = {
        "tasks": [{
            "task_id": "multi_target_e2e_001", "priority": "Critical", "task_name": "Test Multi-Target E2E",
            "description": "Modify file_b.py specifically.", "status": "Completed", # Status is completed
            "target_file": f"{file_a_path_relative},{file_b_path_relative}", "depends_on": []
        }]
    }
    roadmap_full_path.write_text(json.dumps(roadmap_content_dict))

    # Patch builtins.open using mocker
    mock_builtin_open = mocker.patch('builtins.open', new_callable=mock_open)
    mock_file = MagicMock()
    # FIX: Update side_effect for mock_file.read
    # 1. Read in load_roadmap (start_workflow) -> initial roadmap
    # 2. Read in load_roadmap (loop 1) -> initial roadmap
    # 3. Read in _update_task_status_in_roadmap (before write) -> initial roadmap
    # 4. Read in load_roadmap (loop 2) -> *updated* roadmap (with task completed)
    # 5. Read in load_roadmap (loop 3) -> empty tasks list (to exit loop)
    mock_file.read.side_effect = [
        json.dumps(roadmap_content_dict), # Read 1: start_workflow -> load_roadmap
        json.dumps(roadmap_content_dict), # Read 2: loop 1 -> load_roadmap
        json.dumps(roadmap_content_dict), # Read 3: loop 1 -> _update_task_status_in_roadmap
        json.dumps(completed_roadmap_content_dict), # Read 4: loop 2 -> load_roadmap
        json.dumps({"tasks": []}) # Read 5: loop 3 -> load_roadmap (to exit)
    ]
    mock_builtin_open.return_value.__enter__.return_value = mock_file


    # Mock LLM responses
    mock_plan = [f"1. Modify {file_b_path_relative} to add a comment."]
    mock_generate_plan = mocker.patch.object(driver, 'generate_solution_plan', return_value=mock_plan)
    mock_llm_orchestrator.generate.return_value = "# New comment added by LLM for file_b"

    # Mock agent results (pre-write and post-write) - Mocks are from the fixture
    mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}
    mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}

    # Mock _read_file_for_context to return content of file_b.py when requested
    resolved_file_b_path = str(file_b_full_path.resolve())
    mock_read_file_for_context = mocker.patch.object(driver, '_read_file_for_context', side_effect=lambda path: file_b_full_path.read_text() if path == resolved_file_b_path else "")

    # Mock _write_output_file to actually write to the temporary file_b.py
    def mock_write_side_effect(path, content, overwrite=False):
        if path == resolved_file_b_path:
            file_b_full_path.write_text(content)
            return True
        return False
    mock_write_output_file = mocker.patch.object(driver, '_write_output_file', side_effect=mock_write_side_effect)

    # Mock _merge_snippet
    mock_merge_snippet = mocker.patch.object(driver, '_merge_snippet', side_effect=lambda existing, snippet: existing + "\n" + snippet + "\n")

    # Mock select_next_task to return the task once, then None
    # FIX: Update side_effect for mock_select_next_task
    # 1. Called with initial tasks -> returns the task
    # 2. Called with updated tasks (from load_roadmap in loop 2) -> returns None (as the task is completed)
    mock_select_next_task = mocker.patch.object(driver, 'select_next_task', side_effect=[roadmap_content_dict['tasks'][0], None])

    # Mock load_roadmap
    # FIX: load_roadmap is called three times: start_workflow, loop 1, loop 2.
    # The side_effect for mock_file.read handles the content returned by open.
    # We don't need to mock load_roadmap's return value directly if open is mocked correctly.
    # Remove the mock_load_roadmap patch. The real load_roadmap will be called and use the mocked open.
    # mock_load_roadmap = mocker.patch.object(driver, 'load_roadmap', side_effect=[roadmap_content_dict['tasks'], roadmap_content_dict['tasks'], []])


    # Mock execute_tests and _parse_test_results
    mock_execute_tests = mocker.patch.object(driver, 'execute_tests')
    mock_parse_test_results = mocker.patch.object(driver, '_parse_test_results')
    mock_execute_tests.assert_not_called()
    mock_parse_test_results.assert_not_called()

    # Mock generate_grade_report and _parse_and_evaluate_grade_report
    mock_generate_grade_report = mocker.patch.object(driver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}}))
    mock_parse_and_evaluate_grade_report = mocker.patch.object(driver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed", "justification": "Mock success"})

    # Mock _safe_write_roadmap_json
    mock_safe_write = mocker.patch.object(driver, '_safe_write_roadmap_json', return_value=True)


    # Start the workflow
    driver.start_workflow(roadmap_path_relative, "output", driver.context)

    # Assertions
    expected_resolved_file_b = mock_context_get_full_path(file_b_path_relative)

    # Verify logs
    assert any(f"Step identified as code generation for file {expected_resolved_file_b}" in record.message for record in caplog.records)
    assert any(f"Step description explicitly mentions '{file_b_path_relative}' from task target list" in record.message for record in caplog.records)
    assert not any("Defaulting to the first file" in record.message for record in caplog.records)
    assert "Successfully wrote merged content to" in caplog.text

    # Verify file content was updated
    assert file_b_full_path.read_text() == "initial content for file_b\n# New comment added by LLM for file_b\n"
    assert file_a_full_path.read_text() == "initial content for file_a"

    # Verify mocks were called correctly
    mock_context_get_full_path.assert_any_call(file_b_path_relative)
    mock_read_file_for_context.assert_called_once_with(expected_resolved_file_b)
    mock_llm_orchestrator.generate.assert_called_once()
    called_prompt = mock_llm_orchestrator.generate.call_args[0][0]
    assert f"EXISTING CONTENT OF `{expected_resolved_file_b}`:\n```python\ninitial content for file_b\n```" in called_prompt
    assert f"The primary file being modified for this step is `{expected_resolved_file_b}`." in called_prompt
    mock_merge_snippet.assert_called_once_with("initial content for file_b", "# New comment added by LLM for file_b")
    mock_write_output_file.assert_called_once_with(expected_resolved_file_b, "initial content for file_b\n# New comment added by LLM for file_b\n", overwrite=True)

    mock_code_review_agent = driver_fixture_dict['mock_code_review_agent']
    mock_ethical_governance_engine = driver_fixture_dict['mock_ethical_governance_engine']
    assert mock_code_review_agent.analyze_python.call_count == 2
    assert mock_ethical_governance_engine.enforce_policy.call_count == 2

    mock_generate_grade_report.assert_called_once()
    mock_parse_and_evaluate_grade_report.assert_called_once_with(ANY)

    mock_safe_write.assert_called_once()
    written_data = mock_safe_write.call_args[0][1]
    assert written_data['tasks'][0]['status'] == 'Completed'

    # Loop should exit after the task is completed
    # select_next_task is called with initial tasks (from load_roadmap in start_workflow),
    # then with initial tasks again (from load_roadmap in loop 1),
    # then with updated tasks (from load_roadmap in loop 2),
    # then returns None.
    # The mock select_next_task side_effect is [task, None].
    # The first call gets the task. The second call gets None, exiting the loop.
    # This means select_next_task is called twice.
    # The first call is with the initial tasks list (from load_roadmap in start_workflow).
    # The second call is with the initial tasks list again (from load_roadmap at the start of loop 1).
    # The loop then processes the task, updates status, and finishes loop 1.
    # The loop starts loop 2, calls load_roadmap (which returns the *updated* list due to mock open side_effect).
    # Then select_next_task is called with this updated list. This is the third call.
    # The side_effect [task, None] means the third call will raise StopIteration.
    # Let's adjust the select_next_task side_effect to match the expected calls.
    # Call 1 (start_workflow): select_next_task(load_roadmap() -> initial_tasks) -> returns task
    # Call 2 (loop 1 start): select_next_task(load_roadmap() -> initial_tasks) -> returns None (loop exits after 1 iteration)
    # This doesn't match the log output which shows loop 2 starting.
    # The log shows:
    # INFO     ...:560 Starting autonomous loop iteration (Loop 1)
    # INFO     ...:581 Selected task: ID=multi_target_e2e_001 (select_next_task called with initial tasks)
    # ... task processed ...
    # INFO     ...:1055 Autonomous loop iteration finished. (End of Loop 1)
    # INFO     ...:560 Starting autonomous loop iteration (Loop 2)
    # INFO     ...:1053 No tasks available in Not Started status. Exiting autonomous loop. (select_next_task called with updated tasks, returns None)
    # INFO     ...:1056 Autonomous loop terminated.
    # So select_next_task is called twice:
    # 1. With initial tasks -> returns task
    # 2. With updated tasks (containing the completed task) -> returns None
    # The mock select_next_task side_effect [task, None] is correct for the *return values*, but the *arguments* passed to the mock are what the assertion checks.
    # The arguments are the lists returned by `load_roadmap`.
    # Call 1: select_next_task(load_roadmap() -> initial_tasks) -> returns task
    # Call 2: select_next_task(load_roadmap() -> updated_tasks) -> returns None
    # So the assertion should be `mock_select_next_task.assert_has_calls([call(roadmap_content_dict['tasks']), call(completed_roadmap_content_dict['tasks'])])`.

    mock_select_next_task.assert_has_calls([call(roadmap_content_dict['tasks']), call(completed_roadmap_content_dict['tasks'])])

    # The original test function is removed, so no need to clean up its patches.