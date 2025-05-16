# tests/test_phase1_8_features.py

import pytest
import unittest # Keep import for potential other uses, but remove inheritance
from unittest.mock import patch, MagicMock, mock_open, call, ANY
import re
from pathlib import Path
import logging
import json
from datetime import datetime
import subprocess
import sys
import ast # Import ast for syntax check

# Add the src directory to the Python path
# This ensures that 'from core.automation.workflow_driver import ...' works
# Use Pathlib for robust path joining
current_file_dir = Path(__file__).parent
# Adjust path to go up three levels to project root, then into src
src_dir = current_file_dir.parent.parent / 'src'
sys.path.insert(0, str(src_dir.resolve()))


# Assuming WorkflowDriver is in src.core.automation
from core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT, classify_plan_step, CODE_KEYWORDS, CONCEPTUAL_KEYWORDS
import spacy
from spacy.matcher import PhraseMatcher

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from core.agents.code_review_agent import CodeReviewAgent
from core.ethics.governance import EthicalGovernanceEngine

# Set up logging for tests
# Ensure logging is configured only once
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(name)s - %(message)s') # Added %(name)s to see logger name

# Use the correct logger name for the module
logger = logging.getLogger(__name__)

# Define a maximum file size for reading (e.g., 1MB)
# Note: This is redefined here, ideally should be imported or consistent
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion, matching the value in workflow_driver.py
# Note: This is redefined here, ideally should be imported or consistent
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"

# Fixture for a WorkflowDriver instance with a Context, specifically for Phase 1.8 tests
@pytest.fixture
def test_driver_phase1_8(tmp_path):
    # Create the actual Context object
    context = Context(str(tmp_path))

    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation
    with patch('core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:
        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value

        driver = WorkflowDriver(context) # Use the 'context' object here

        # Ensure LLM orchestrator mock is set up
        driver.llm_orchestrator = MagicMock()
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"

        # Assign mocked instances
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        # Manually set default_policy_config as _load_default_policy might be complex to mock fully here
        driver.default_policy_config = {'policy_name': 'Mock Policy'}

        # Add attributes needed for tests that might not be set by __init__ or autonomous_loop setup
        driver._current_task_results = {}
        driver.remediation_attempts = 0
        driver.remediation_occurred_in_pass = False
        driver._current_task = {}
        driver.task_target_file = None

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance
        }

# Helper function to simulate the relevant part of autonomous_loop for testing classification
# REMOVED: This helper is no longer needed as tests will call driver methods directly.
# def check_step_classification(driver_instance, step_text, task_target_file=None):
#     ...

class TestPhase1_8Features:
    # These tests now call the driver's preliminary classification method
    def test_research_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Research and identify keywords for src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False
        # Filepath determination is now tested separately below

    def test_code_generation_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Implement the new function in src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is True
        # Filepath determination is now tested separately below

    def test_explicit_file_writing_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Write the research findings to research_summary.md"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is True # "Write" is also a code keyword, but "research" dominates
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is True
        # Filepath determination is now tested separately below

    def test_test_execution_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Run tests for the new feature."
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is False # "Run tests" is not code gen
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is False
        assert prelim_flags["is_test_execution_step_prelim"] is True
        # Filepath determination is now tested separately below

    def test_conceptual_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8['driver']
        step1 = "Discuss the design approach with the team."
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False # "Discuss" is conceptual
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is False # Added check
        assert prelim_flags["is_test_execution_step_prelim"] is False # Added check
        assert prelim_flags["is_test_writing_step_prelim"] is False # Added check


    @patch.object(WorkflowDriver, '_write_output_file')
    def test_conceptual_define_step_does_not_overwrite_main_python_target(self, mock_write_output, test_driver_phase1_8, tmp_path, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        driver._current_task = {
            'task_id': 'test_conceptual_write', 'task_name': 'Test Conceptual Write',
            'description': 'A test.', 'status': 'Not Started', 'priority': 'High',
            'target_file': 'src/core/automation/workflow_driver.py'
        }
        driver.task_target_file = driver._current_task['target_file'] # Set task_target_file on driver
        plan_step = "Write a define list of keywords for step classification."

        # Call the new driver methods
        prelim_flags = driver._classify_step_preliminary(plan_step)
        filepath_to_use = driver._determine_filepath_to_use(plan_step, driver.task_target_file, prelim_flags)
        content_to_write_decision, overwrite_mode = driver._determine_write_operation_details(plan_step, filepath_to_use, driver.task_target_file, prelim_flags)

        # Assertions
        assert content_to_write_decision is None
        mock_write_output.assert_not_called()
        # Assert on the log message generated by the driver method
        expected_log_message = "Skipping placeholder write to main Python target src/core/automation/workflow_driver.py for conceptual step: 'Write a define list of keywords for step classification.'."
        assert any(expected_log_message in record.message for record in caplog.records)


class TestPreWriteValidation:
    @pytest.fixture
    def driver_pre_write(self, mocker, tmp_path): # Added tmp_path
        mock_context = Context(str(tmp_path)) # Use tmp_path for context
        with patch('core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
             patch('core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
             patch('core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator:
            mock_code_review_agent_instance = MockCodeReviewAgent.return_value
            mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
            mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value
            mocker.patch.object(WorkflowDriver, '_load_default_policy')
            wd = WorkflowDriver(mock_context)
            wd.code_review_agent = mock_code_review_agent_instance
            wd.ethical_governance_engine = mock_ethical_governance_engine_instance
            wd.llm_orchestrator = mock_llm_orchestrator_instance
            wd.default_policy_config = {'policy_name': 'Mock Policy'}
            wd._current_task_results = {'step_errors': []}
            wd._current_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Mock Description', 'status': 'Not Started', 'priority': 'medium', 'target_file': 'src/mock_file.py'}
            wd.task_target_file = wd._current_task['target_file']
            mocker.patch.object(wd, '_read_file_for_context', return_value="")
            mocker.patch.object(wd, '_merge_snippet', side_effect=lambda _, snippet: snippet) # Simple merge
            # Mock the new classification/determination methods if they were used in _simulate_step_execution_for_pre_write_validation
            # However, _simulate_step_execution_for_pre_write_validation only simulates the *validation* block,
            # which happens *after* path determination and content decision. So, no need to mock those here.
            yield wd

    def _simulate_step_execution_for_pre_write_validation(self, driver, generated_snippet, step_description="Step 1: Implement code in src/mock_file.py"):
        """Helper to simulate the pre-write validation block within autonomous_loop."""
        # This helper simulates the block *after* filepath_to_use is determined and content_to_write is decided.
        # It focuses only on the validation logic.
        filepath_to_use = driver.task_target_file # Assume filepath_to_use is already set

        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
        validation_passed = True
        validation_feedback = []

        # 1. Syntax Check (using AST parse)
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

        # 2. Ethical Check (if policy loaded and syntax passed)
        if validation_passed and driver.default_policy_config:
            try:
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

        # 3. Code Style/Security Check
        if validation_passed:
            try:
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
            # Simulate adding error to results if needed for other tests, though this helper just raises
            # driver._current_task_results['step_errors'].append(...)
            raise ValueError(f"Pre-write validation failed for step.") # Raise error to be caught by retry logic
        else:
            logger.info(f"Pre-write validation passed for snippet targeting {filepath_to_use}. Proceeding with merge/write.")
            # Simulate write and post-write validations if needed for the test
            driver._write_output_file(filepath_to_use, generated_snippet, overwrite=True) # Use generated_snippet directly for simplicity
            # Simulate post-write validations being called
            driver.code_review_agent.analyze_python(generated_snippet)
            if driver.default_policy_config:
                driver.ethical_governance_engine.enforce_policy(generated_snippet, driver.default_policy_config)


    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    def test_pre_write_validation_all_pass(self, mock_write, driver_pre_write, caplog):
        caplog.set_level(logging.INFO)
        driver = driver_pre_write
        snippet = "def generated_code(): pass"
        driver.ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        driver.code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}

        self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        assert "Pre-write syntax check (AST parse) passed" in caplog.text
        assert "Pre-write ethical validation passed" in caplog.text
        assert "Pre-write style/security validation passed" in caplog.text
        assert "Pre-write validation passed for snippet targeting src/mock_file.py. Proceeding with merge/write." in caplog.text
        mock_write.assert_called_once_with("src/mock_file.py", snippet, overwrite=True)
        assert not driver._current_task_results['step_errors']

    @patch.object(WorkflowDriver, '_write_output_file')
    def test_pre_write_validation_syntax_fails(self, mock_write, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write
        snippet = "def invalid syntax"

        with pytest.raises(ValueError, match="Pre-write validation failed for step."):
            self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        mock_write.assert_not_called()
        # Assert on a substring of the expected error message
        assert "Pre-write syntax validation (AST parse) failed for snippet:" in caplog.text
        assert f"Failed snippet:\n---\n{snippet}\n---" in caplog.text
        assert "Pre-write validation failed for snippet targeting src/mock_file.py. Skipping write/merge." in caplog.text

    @patch.object(WorkflowDriver, '_write_output_file')
    def test_pre_write_validation_ethical_fails(self, mock_write, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write
        snippet = "def generated_code(): pass"
        driver.ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}

        with pytest.raises(ValueError, match="Pre-write validation failed for step."):
            self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        mock_write.assert_not_called()
        assert "Pre-write ethical validation failed for snippet" in caplog.text
        assert f"Failed snippet:\n---\n{snippet}\n---" in caplog.text
        assert "Pre-write validation failed for snippet targeting src/mock_file.py. Skipping write/merge." in caplog.text

    @patch.object(WorkflowDriver, '_write_output_file')
    def test_pre_write_validation_style_fails(self, mock_write, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_pre_write
        snippet = "def generated_code(): pass"
        driver.ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        driver.code_review_agent.analyze_python.return_value = {'status': 'failed', 'static_analysis': [{'severity': 'error', 'code': 'E302', 'message': 'expected 2 blank lines'}]}

        with pytest.raises(ValueError, match="Pre-write validation failed for step."):
            self._simulate_step_execution_for_pre_write_validation(driver, snippet)

        mock_write.assert_not_called()
        assert "Pre-write style/security validation failed for snippet" in caplog.text
        assert f"Failed snippet:\n---\n{snippet}\n---" in caplog.text
        assert "Pre-write validation failed for snippet targeting src/mock_file.py. Skipping write/merge." in caplog.text

    # --- Tests for task_1_8_2c_target_test_file_for_test_writing_steps ---
    # These tests now call the driver's file path determination method
    def test_test_writing_step_uses_explicit_test_file_path(self, test_driver_phase1_8, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        driver._current_task = {'task_id': 'test_task', 'task_name': 'Test Task', 'description': 'Desc', 'status': 'Not Started', 'priority': 'high', 'target_file': 'src/module.py'}
        driver.task_target_file = driver._current_task['target_file'] # Set task_target_file on driver
        step = "Step 1: Write unit tests for src/module.py in tests/test_module.py"

        prelim_flags = driver._classify_step_preliminary(step)
        filepath_to_use = driver._determine_filepath_to_use(step, driver.task_target_file, prelim_flags)

        assert filepath_to_use == "tests/test_module.py"
        expected_log_message = "Test writing step: Using explicit test path from step 'tests/test_module.py'."
        assert any(expected_log_message in record.message for record in caplog.records)


    def test_test_writing_step_derives_path_from_task_target(self, test_driver_phase1_8, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        driver._current_task = {'task_id': 'test_task', 'task_name': 'Test Task', 'description': 'Desc', 'status': 'Not Started', 'priority': 'high', 'target_file': 'src/another_module.py'}
        driver.task_target_file = driver._current_task['target_file'] # Set task_target_file on driver
        step = "Step 1: Write unit tests for src/another_module.py"

        prelim_flags = driver._classify_step_preliminary(step)
        filepath_to_use = driver._determine_filepath_to_use(step, driver.task_target_file, prelim_flags)

        assert filepath_to_use == "tests/test_another_module.py"
        expected_log_message = "Test writing step: Derived test file path 'tests/test_another_module.py' from task target 'src/another_module.py'."
        assert any(expected_log_message in record.message for record in caplog.records)


    def test_test_writing_step_uses_task_target_if_already_test_file(self, test_driver_phase1_8, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        driver._current_task = {'task_id': 'test_task', 'task_name': 'Test Task', 'description': 'Desc', 'status': 'Not Started', 'priority': 'high', 'target_file': 'tests/test_existing.py'}
        driver.task_target_file = driver._current_task['target_file'] # Set task_target_file on driver
        step = "Step 1: Update unit tests in tests/test_existing.py"

        prelim_flags = driver._classify_step_preliminary(step)
        filepath_to_use = driver._determine_filepath_to_use(step, driver.task_target_file, prelim_flags)

        assert filepath_to_use == "tests/test_existing.py"
        expected_log_message = "Test writing step: Using task_target_file as it appears to be a test file 'tests/test_existing.py'."
        assert any(expected_log_message in record.message for record in caplog.records)


    def test_test_writing_step_without_task_target_uses_step_path(self, test_driver_phase1_8, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        driver._current_task = {'task_id': 'test_task', 'task_name': 'Test Task', 'description': 'Desc', 'status': 'Not Started', 'priority': 'high', 'target_file': None}
        driver.task_target_file = driver._current_task['target_file'] # Set task_target_file on driver
        step = "Step 1: Write unit tests in tests/test_new_feature.py"

        prelim_flags = driver._classify_step_preliminary(step)
        filepath_to_use = driver._determine_filepath_to_use(step, driver.task_target_file, prelim_flags)

        assert filepath_to_use == "tests/test_new_feature.py"
        # Note: The log message for this case is "Using explicit test path from step"
        expected_log_message = "Test writing step: Using explicit test path from step 'tests/test_new_feature.py'."
        assert any(expected_log_message in record.message for record in caplog.records)


    def test_non_test_writing_step_uses_task_target(self, test_driver_phase1_8, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        driver._current_task = {'task_id': 'test_task', 'task_name': 'Test Task', 'description': 'Desc', 'status': 'Not Started', 'priority': 'high', 'target_file': 'src/module.py'}
        driver.task_target_file = driver._current_task['target_file'] # Set task_target_file on driver
        step = "Step 1: Implement feature in src/module.py"

        prelim_flags = driver._classify_step_preliminary(step)
        filepath_to_use = driver._determine_filepath_to_use(step, driver.task_target_file, prelim_flags)

        assert filepath_to_use == "src/module.py"
        # No specific log for this case in _determine_filepath_to_use

    def test_non_test_writing_step_without_task_target_uses_step_path(self, test_driver_phase1_8, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver']
        driver._current_task = {'task_id': 'test_task', 'task_name': 'Test Task', 'description': 'Desc', 'status': 'Not Started', 'priority': 'high', 'target_file': None}
        driver.task_target_file = driver._current_task['target_file'] # Set task_target_file on driver
        step = "Step 1: Implement feature in src/new_module.py"

        prelim_flags = driver._classify_step_preliminary(step)
        filepath_to_use = driver._determine_filepath_to_use(step, driver.task_target_file, prelim_flags)

        assert filepath_to_use == "src/new_module.py"
        # No specific log for this case in _determine_filepath_to_use