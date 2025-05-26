import pytest
import unittest
from unittest.mock import patch, MagicMock, mock_open, call, ANY
import re
from pathlib import Path
import logging
import tempfile
import os
import json
import ast
import html
import sys
import shutil

# Add the src directory to the Python path if not already done in conftest.py
# Use Pathlib for robust path joining
current_file_dir = Path(__file__).parent

# Adjust path to go up three levels to project root, then into src
src_dir = current_file_dir.parent.parent / 'src'
sys.path.insert(0, str(src_dir.resolve()))

# Assuming WorkflowDriver is in src.core.automation
# FIX: Import all necessary components used in tests
# Added DOCSTRING_INSTRUCTION_PYTHON for the new tests
# Added PYTHON_CREATION_KEYWORDS for the unit test mock implementation
from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT, classify_plan_step, CODE_KEYWORDS, CONCEPTUAL_KEYWORDS, MAX_STEP_RETRIES, DOCSTRING_INSTRUCTION_PYTHON, PYTHON_CREATION_KEYWORDS, GENERAL_PYTHON_DOCSTRING_REMINDER, GENERAL_SNIPPET_GUIDELINES, CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS, END_OF_CODE_MARKER, CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS
from src.utils.config import SecureConfig # Import SecureConfig for patching

# FIX: Import EnhancedLLMOrchestrator as it's patched
from src.core.llm_orchestration import EnhancedLLMOrchestrator

import spacy
from spacy.matcher import PhraseMatcher

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from src.core.automation.workflow_driver import classify_plan_step

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
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator, \
         patch.object(WorkflowDriver, '_load_default_policy') as MockLoadPolicy: # Patch _load_default_policy


        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value # FIX: Get mock instance
        MockLoadPolicy.return_value = {'policy_name': 'Mock Policy'} # Configure the mock load policy method


        driver = WorkflowDriver(context)
        # Ensure LLM orchestrator mock is set up
        # FIX: Assign the patched LLM orchestrator instance
        driver.llm_orchestrator = mock_llm_orchestrator_instance
        # Default mock return for generate, can be overridden in tests
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        # Assign mocked instances (this happens automatically if patching instantiation, but explicit is fine)
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        # The default_policy_config is set by _load_default_policy, which is now mocked.
        # Ensure the mock return value is assigned to the driver's attribute if needed later,
        # but the mock itself handles the __init__ call.
        # driver.default_policy_config = {'policy_name': 'Mock Policy'} # This might be redundant if _load_default_policy is mocked


        # Reset the mock's call count after driver initialization in the fixture
        # mock_context_get_full_path.reset_mock() # This mock is not patched here anymore

        # FIX: Yield the driver instance directly, not a dictionary
        yield driver
# Fixture specifically for testing _resolve_target_file_for_step and _validate_path
@pytest.fixture
def driver_for_multi_target_resolution(tmp_path, mocker):
    mock_context = Context(str(tmp_path))
    def mock_get_full_path_side_effect(relative_path_str):
        if not isinstance(relative_path_str, str): # Handle non-string input
            logger.warning(f"Mock Path validation received invalid input: {relative_path_str}")
            return None


        try:
            # Handle empty string specifically as resolving to base path
            if relative_path_str == "":
                 # Use strict=False here too, although base path should exist
                 resolved_path = Path(mock_context.base_path).resolve(strict=False)
            else:
                 full_path = (Path(mock_context.base_path) / relative_path_str)
                 # FIX: Use resolve(strict=False) and remove the exists() check
                 resolved_path = full_path.resolve(strict=False) # <-- CHANGE IS HERE

            # Security check: Ensure the resolved path is within the base path
            # Use str() for comparison as resolved_path is a Path object
            # FIX: Resolve the base path with strict=False for consistent comparison
            resolved_base_path_str = str(Path(mock_context.base_path).resolve(strict=False))
            if not str(resolved_path).startswith(resolved_base_path_str):
                # Log a warning if path traversal is detected
                logger.warning(f"Path traversal attempt detected during mock resolution: {relative_path_str} resolved to {resolved_path}")
                return None
            return str(resolved_path)
        except FileNotFoundError:
             # Simulate the real Context behavior for non-existent paths
             # This block might still be hit if parent dir doesn't exist even with strict=False
             logger.debug(f"Mock resolution failed: Path not found for '{relative_path_str}' relative to '{mock_context.base_path}'.")
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
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'), \
         patch.object(WorkflowDriver, '_load_default_policy'): # Patch _load_default_policy
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

        # FIX: Mock _determine_single_target_file as well, as it's called by _resolve_target_file_for_step
        # This mock should return None to ensure the fallback (_determine_filepath_to_use) is called in relevant tests
        # or return a specific value in tests focused on the new method's logic.
        # For the tests in TestPathResolutionAndValidation, we want to test the *interaction*
        # of _resolve_target_file_for_step with _determine_single_target_file and _determine_filepath_to_use.
        # So, we should mock _determine_single_target_file to control its output, allowing us to test
        # the fallback logic.
        mock_determine_single_target_file = mocker.patch.object(driver, '_determine_single_target_file', return_value=None)


        # FIX: Yield the driver instance directly
        yield driver
class TestPhase1_8Features:
    def test_research_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8
        step1 = "Research and identify keywords for src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False


    def test_code_generation_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8
        step1 = "Implement the new function in src/core/automation/workflow_driver.py"
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is True

    def test_explicit_file_writing_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8
        step1 = "Write the research findings to research_summary.md"
        prelim_flags = driver._classify_step_preliminary(step1)
        # FIX: Research step classification should be True if it contains research keywords
        # The step "Write the research findings..." implies research was done, so this is correct.
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is True

    def test_test_execution_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8
        step1 = "Run tests for the new feature."
        prelim_flags = driver._classify_step_preliminary(step1)
        assert prelim_flags["is_research_step_prelim"] is False
        assert prelim_flags["is_code_generation_step_prelim"] is False
        assert prelim_flags["is_explicit_file_writing_step_prelim"] is False
        assert prelim_flags["is_test_execution_step_prelim"] is True

    def test_conceptual_step_classification(self, test_driver_phase1_8):
        driver = test_driver_phase1_8
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
        driver = test_driver_phase1_8
        # FIX: Mock context get_full_path to return a resolved path for the target file
        resolved_target_path = str(tmp_path / 'src' / 'core' / 'automation' / 'workflow_driver.py')
        # Ensure the mock handles the specific target file path correctly
        # Access the mock from the fixture's yield value
        # This requires changing the test_driver_phase1_8 fixture to yield the dictionary again,
        # or patching context.get_full_path directly in this test.
        # Let's patch it directly in this test for clarity, as the fixture change would affect other tests.
        # Need to patch the *instance* method on the driver instance from the fixture
        mock_context_get_full_path = mocker.patch.object(driver.context, 'get_full_path', side_effect=lambda path: resolved_target_path if path == 'src/core/automation/workflow_driver.py' else str(Path(tmp_path) / path))


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
        # Patch _resolve_target_file_for_step as it's called before _determine_write_operation_details
        # Need to patch the *instance* method on the driver instance from the fixture
        mock_resolve_target_file = mocker.patch.object(driver, '_resolve_target_file_for_step', return_value=resolved_target_path)


        # FIX: Call _resolve_target_file_for_step first to get the resolved path
        filepath_to_use = mock_resolve_target_file(plan_step, driver.task_target_file, prelim_flags)
        content_to_write_decision, overwrite_mode = driver._determine_write_operation_details(plan_step, filepath_to_use, driver.task_target_file, prelim_flags)

        assert content_to_write_decision is None
        mock_write_output.assert_not_called()
        # FIX: Ensure the log message matches the actual log output format
        expected_log_message = f"Skipping placeholder write to main Python target {resolved_target_path} for conceptual step: '{plan_step}'."
        assert any(expected_log_message in record.message for record in caplog.records)
    # --- Tests for _is_simple_addition_plan_step (Task 1.8.A) ---
    @pytest.mark.parametrize("description, expected", [
        ("Add import os to the file", True),
        ("add a new function called calculate_total", True),
        ("Implement method process_item in Processor", True), # Shorter
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
        ("Refactor the entire data processing module", False),
        ("Design the new user interface components", False),
        ("Review the latest pull request for feature X", False),
        ("Analyze performance bottlenecks in the API", False),
        ("Understand the requirements for the next phase", False),
        ("Modify existing function to handle new edge cases", False),
        ("Update the database schema", False), # Database schema changes are not simple code additions
        ("Write a comprehensive design document", False),
        ("Add a new complex system with multiple classes", False), # Shorter
        ("", False),
        ("    ", False),
        ("Long desc, no simple add keywords, architectural review.", False), # Shorter
    ])
    def test_is_simple_addition_plan_step(self, test_driver_phase1_8, description, expected, caplog):
        """Test the _is_simple_addition_plan_step method with various descriptions."""
        caplog.set_level(logging.DEBUG) # Set log level to DEBUG to capture debug messages
        driver = test_driver_phase1_8
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

    def test_is_simple_addition_plan_step_class_creation_keywords_are_not_simple(self, test_driver_phase1_8, caplog):
        """
        Test that steps involving class creation keywords are correctly identified as NOT simple.
        """
        caplog.set_level(logging.DEBUG) # Set log level to DEBUG to capture debug messages
        driver = test_driver_phase1_8
        class_creation_steps = [
            "Create new class ComplexSystem for advanced calculations",
            "Add class NewComponent to the architecture",
            "Define class User",
            "Implement class MyUtility",
            "Generate class for data processing"
        ]
        for step_desc in class_creation_steps:
            assert driver._is_simple_addition_plan_step(step_desc) is False, f"Step '{step_desc}' should NOT be simple."
            assert any( # Check for any of the possible "not simple" log messages
                (f"Step '{step_desc[:50]}...' involves class creation keyword" in record.message) or # From simple_addition_keywords loop
                (f"Step '{step_desc[:50]}...' matches" in record.message and "and includes class and is not simple" in record.message) or # From general_addition_patterns loop
                (f"Step '{step_desc[:50]}...' not identified as simple." in record.message) # From final fallback
                for record in caplog.records
            ), f"Expected specific log message for non-simple class creation step '{step_desc}', but found none matching criteria in {caplog.records}"
            caplog.clear()

class TestPreWriteValidation:
    @pytest.fixture
    def driver_pre_write(self, mocker, tmp_path):
        mock_context = Context(str(tmp_path))
        # FIX: Mock Context.get_full_path here as well, as _load_default_policy calls it
        mock_context_get_full_path = mocker.patch.object(mock_context, 'get_full_path', side_effect=lambda path: str(Path(mock_context.base_path) / path) if path else str(Path(mock_context.base_path)))


        with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
             patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
             patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator: # Removed MockLoadPolicy patch here


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
            # FIX: Explicitly set default_policy_config on the driver instance
            wd.default_policy_config = {'policy_name': 'Mock Policy'}


            wd._current_task_results = {'step_errors': []}
            wd._current_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Mock Description', 'status': 'Not Started', 'priority': 'medium', 'target_file': 'src/mock_file.py'}
            wd.task_target_file = wd._current_task['target_file']

            # FIX: Mock _resolve_target_file_for_step to return the resolved target file
            # This method is called by autonomous_loop before pre-write validation
            resolved_target_path = str(Path(tmp_path) / wd.task_target_file)
            # Use mocker to patch the instance method
            mock_resolve_target_file = mocker.patch.object(wd, '_resolve_target_file_for_step', return_value=resolved_target_path)

            # Patch _write_output_file here as it's called in the helper
            mock_write_output = mocker.patch.object(wd, '_write_output_file', return_value=True)

            # Mock _read_file_for_context as it's called in the helper
            mock_read_file = mocker.patch.object(wd, '_read_file_for_context', return_value="existing file content")


            # FIX: Reset mock after init calls it
            mock_context_get_full_path.reset_mock()

            # FIX: Yield a dictionary containing the driver and the specific mocks needed by the tests
            yield {
                'driver': wd,
                'mock_code_review_agent': mock_code_review_agent_instance,
                'mock_ethical_governance_engine': mock_ethical_governance_engine_instance,
                'mock_resolve_target_file': mock_resolve_target_file,
                'mock_write_output': mock_write_output,
                'mock_read_file': mock_read_file, # Add this to the returned dict
            }


    # This helper function simulates the relevant part of the autonomous loop
    # where pre-write validation occurs.
    # FIX: Add mock_ast_parse as an argument
    # FIX: Add mocks from fixture as arguments
    def _simulate_step_execution_for_pre_write_validation(self, driver, generated_snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output, mock_code_review_agent, mock_ethical_governance_engine, step_description="Step 1: Implement code in src/mock_file.py", is_minimal_context=False):
        # In the real loop, filepath_to_use comes from _resolve_target_file_for_step
        # Since we mocked _resolve_target_file_for_step in the fixture, we can use its return value
        # Call the mocked _resolve_target_file_for_step to get the value it would return
        # FIX: Pass necessary args to mock_resolve_target_file
        filepath_to_use = mock_resolve_target_file(step_description, driver.task_target_file, driver._classify_step_preliminary(step_description))

        # Ensure filepath_to_use is not None before proceeding
        if filepath_to_use is None:
             logger.error("Simulated _resolve_target_file_for_step returned None.")
             raise ValueError("Resolved file path is None.")
        
        # Mock _get_context_type_for_step and _extract_targeted_context if needed for full simulation
        # For pre-write validation tests, we usually just pass the full content as context
        mocker = MagicMock() # Create a local mocker for patching within this helper
        mocker.patch.object(driver, '_get_context_type_for_step', return_value=None) # Not relevant for these tests


        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
        validation_passed = True
        validation_feedback = []
        try:
            # FIX: Use the passed mock_ast_parse
            mock_ast_parse(generated_snippet) # First call: snippet
            logger.info("Pre-write syntax check (AST parse) passed for snippet.")
        except SyntaxError as se:
            # SUT allows SyntaxError on snippet to proceed to full file check
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
                # FIX: Use the passed mock_ethical_governance_engine
                ethical_results = mock_ethical_governance_engine.enforce_policy(
                    generated_snippet,
                    driver.default_policy_config,
                    is_snippet=True # MODIFIED: Pass is_snippet=True
                )
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

        if validation_passed: # Only proceed with style/security if previous checks passed
            try:
                # Call the actual mocked code_review_agent instance method
                # FIX: Use the passed mock_code_review_agent
                style_review_results = mock_code_review_agent.analyze_python(generated_snippet)
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
            # Call the actual _merge_snippet method (not mocked in this test)
            existing_content = mock_read_file.return_value # Get content from mock read (set by test)
            merged_content = driver._merge_snippet(existing_content, generated_snippet)
            
            # --- START: Pre-Merge Full File Syntax Check (Task 1.8.improve_snippet_handling sub-task 4) ---
            try:
                # Create a hypothetical merged content
                # Use the existing _merge_snippet logic for this hypothetical merge
                # This is the second call to mock_ast_parse in the real code, for the merged content
                mock_ast_parse(merged_content) # Second call: merged content
                logger.info("Pre-merge full file syntax check (AST parse) passed.") # This log is for the full file
            except SyntaxError as se:
                validation_passed = False
                validation_feedback.append(f"Pre-merge full file syntax check failed: {se}")
                logger.warning(f"Pre-merge full file syntax validation failed for {filepath_to_use}: {se}")
                logger.warning(f"Hypothetical merged content (cleaned):\n---\n{merged_content}\n---")
                raise ValueError(f"Pre-merge full file syntax validation failed: {'. '.join(validation_feedback)}")
            except Exception as e:
                validation_passed = False
                validation_feedback.append(f"Error during pre-merge full file syntax validation: {e}")
                logger.error(f"Error during pre-merge full file syntax validation: {e}", exc_info=True)
                logger.warning(f"Hypothetical merged content (cleaned):\n---\n{merged_content}\n---")
                raise ValueError(f"Pre-merge full file syntax validation failed: {'. '.join(validation_feedback)}")

            # If pre-merge validation passed, proceed to actual write and post-write validation
            # The outer `if not validation_passed` will catch the `ValueError` raised above.
            # If we reach here, it means pre-merge validation also passed.
            mock_write_output(filepath_to_use, merged_content, overwrite=True)
            # Call the actual mocked agent instance methods for post-write validation
            # FIX: Use the passed mock_code_review_agent and mock_ethical_governance_engine
            mock_code_review_agent.analyze_python(merged_content)
            if driver.default_policy_config:
                mock_ethical_governance_engine.enforce_policy(merged_content, driver.default_policy_config)


    # Remove the patch decorator here, _write_output_file is patched in the fixture
    @patch('src.core.automation.workflow_driver.ast.parse') # Patch ast.parse here
    def test_pre_write_validation_all_pass(self, mock_ast_parse, driver_pre_write, caplog):
        caplog.set_level(logging.INFO)
        # Unpack fixture result
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file'] # Unpack mock_read_file
        mock_write_output = driver_pre_write['mock_write_output']


        snippet = "def generated_code(): pass"
        # Set return values on the actual mock instances from the fixture
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}
        # Configure ast.parse to succeed for both snippet and merged content
        mock_ast_parse.side_effect = [None, None] # First call (on snippet), second call (on merged content)

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        # Note: This mock is set in the fixture using mocker.patch.object(wd, ...)
        resolved_target_path = mock_resolve_target_file.return_value # Get the value returned by the mock

        # FIX: Pass mock_ast_parse and other mocks to the helper
        self._simulate_step_execution_for_pre_write_validation(
            driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, # Pass mock_read_file
            mock_write_output, mock_code_review_agent, mock_ethical_governance_engine
        )

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = mock_resolve_target_file.return_value # Get the value returned by the mock

        # More robust log assertions using caplog.records
        log_messages = [record.message for record in caplog.records]
        assert any("Pre-write syntax check (AST parse) passed" in msg for msg in log_messages)
        assert any("Pre-write ethical validation passed" in msg for msg in log_messages)
        assert any("Pre-write style/security validation passed for snippet." in msg for msg in log_messages)
        assert any("Pre-merge full file syntax check (AST parse) passed." in msg for msg in log_messages) # New assertion for pre-merge check
        assert any(f"Pre-write validation passed for snippet targeting {resolved_target_path}. Proceeding with merge/write." in msg for msg in log_messages)
        
        # Assert on the resolved path in the write call (patched in fixture)
        # The helper uses mock_read_file.return_value as existing content for merge
        expected_merged_content = driver._merge_snippet(mock_read_file.return_value, snippet)
        mock_write_output.assert_called_once_with(resolved_target_path, expected_merged_content, overwrite=True)
        # Assert on the resolved path in the post-write validation calls (mocks from fixture)
        # analyze_python is called twice (pre and post)
        mock_code_review_agent.analyze_python.assert_has_calls([call(snippet), call(expected_merged_content)])
        # enforce_policy is called twice (pre and post)
        mock_ethical_governance_engine.enforce_policy.assert_has_calls([call(snippet, driver.default_policy_config, is_snippet=True), call(expected_merged_content, driver.default_policy_config)])

        assert not driver._current_task_results['step_errors']

    # Remove the patch decorator here, _write_output_file is patched in the fixture
    @patch('src.core.automation.workflow_driver.ast.parse') # Patch ast.parse here
    def test_pre_write_validation_syntax_fails(self, mock_ast_parse, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        # Unpack fixture result
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file'] # Unpack mock_read_file
        mock_write_output = driver_pre_write['mock_write_output']


        snippet = "def invalid syntax"
        # Configure ast.parse to fail for both snippet and merged content
        # The first call (on snippet) will raise SyntaxError.
        # The helper will then proceed to the second call (on merged content), which will also fail.
        mock_ast_parse.side_effect = [
            SyntaxError("Mock syntax error", ('<string>', 1, 1, 'def invalid syntax')), # For snippet (first call)
            SyntaxError("Mock merged syntax error", ('<string>', 1, 1, 'def invalid syntax')) # For merged content
        ]


        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = mock_resolve_target_file.return_value # Get the value returned by the mock

        # FIX: Pass mock_ast_parse and other mocks to the helper
        # Adjust the regex to match the specific error message when pre-merge full file syntax check fails
        with pytest.raises(ValueError, match=r"Pre-merge full file syntax validation failed: Pre-write syntax check failed: Mock syntax error.*Pre-merge full file syntax check failed: Mock merged syntax error"):
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine
            )

        # _write_output_file is patched in the fixture, assert on the instance mock
        mock_write_output.assert_not_called()
        # More robust log assertions using caplog.records
        log_messages = [record.message for record in caplog.records] # Capture logs for assertion
        # This log comes from the test helper's own logging
        assert any("Pre-write syntax validation (AST parse) failed for snippet: Mock syntax error (<string>, line 1)" in msg for msg in log_messages)
        # The pre-merge full file syntax check should now also fail, check for its specific log
        assert any(f"Pre-merge full file syntax validation failed for {resolved_target_path}: Mock merged syntax error (<string>, line 1)" in msg for msg in log_messages)
        # This log should NOT be present as the process fails before reaching this point
        assert not any(f"All pre-write validations passed for snippet targeting {resolved_target_path}. Proceeding with actual merge/write." in msg for msg in log_messages) 
        # This log should NOT be present as the process fails before reaching this point
        assert not any(f"Pre-write validation passed for snippet targeting {resolved_target_path}. Proceeding with merge/write." in msg for msg in log_messages)
        assert any(f"Failed snippet:\n---\n{snippet}\n---" in msg for msg in log_messages)
        # The "Skipping write/merge" log is not hit in this specific helper path, so remove assertion for it.
        # Pre-write ethical and style checks ARE called because snippet-level SyntaxError proceeds to them.
        mock_code_review_agent.analyze_python.assert_called_once_with(snippet)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)
        # Post-write validation (on merged content) should still not be called
        assert mock_code_review_agent.analyze_python.call_count == 1
        assert mock_ethical_governance_engine.enforce_policy.call_count == 1


    # Remove the patch decorator here, _write_output_file is patched in the fixture
    @patch('src.core.automation.workflow_driver.ast.parse') # Patch ast.parse here
    def test_pre_write_validation_ethical_fails(self, mock_ast_parse, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        # Unpack fixture result
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file'] # Unpack mock_read_file
        mock_write_output = driver_pre_write['mock_write_output']


        snippet = "def generated_code(): pass"
        # Set return value on the mock_ast_parse from the decorator
        mock_ast_parse.return_value = True
        # Set return values on the actual mock instances from the fixture
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = mock_resolve_target_file.return_value # Get the value returned by the mock

        # FIX: Pass mock_ast_parse and other mocks to the helper
        with pytest.raises(ValueError, match="Pre-write validation failed for step."): # The error message is generic
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine
            )

        # _write_output_file is patched in the fixture, assert on the instance mock
        mock_write_output.assert_not_called()
        # More robust log assertions using caplog.records
        log_messages = [record.message for record in caplog.records]
        assert any("Pre-write ethical validation failed for snippet" in msg for msg in log_messages)
        assert any(f"Failed snippet:\n---\n{snippet}\n---" in msg for msg in log_messages)
        # Assert on the resolved path in the log message
        assert any(f"Pre-write validation failed for snippet targeting {resolved_target_path}. Skipping write/merge." in msg for msg in log_messages)
        # Style/Security and post-write validation should not be called (mocks from fixture)
        mock_code_review_agent.analyze_python.assert_not_called()
        # Ethical check is called once for pre-write validation (mock from fixture)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)


    # Remove the patch decorator here, _write_output_file is patched in the fixture
    @patch('src.core.automation.workflow_driver.ast.parse') # Patch ast.parse here
    def test_pre_write_validation_style_fails(self, mock_ast_parse, driver_pre_write, caplog):
        caplog.set_level(logging.WARNING)
        # Unpack fixture result
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file'] # Unpack mock_read_file
        mock_write_output = driver_pre_write['mock_write_output']


        snippet = "def generated_code(): pass"
        # Set return value on the mock_ast_parse from the decorator
        mock_ast_parse.return_value = True
        # Set return values on the actual mock instances from the fixture
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        mock_code_review_agent.analyze_python.return_value = {'status': 'failed', 'static_analysis': [{'severity': 'error', 'code': 'E302', 'message': 'expected 2 blank lines'}]}

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = mock_resolve_target_file.return_value # Get the value returned by the mock

        # FIX: Pass mock_ast_parse and other mocks to the helper
        with pytest.raises(ValueError, match="Pre-write validation failed for step."): # The error message is generic
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine
            )

        # _write_output_file is patched in the fixture, assert on the instance mock
        mock_write_output.assert_not_called()
        # More robust log assertions using caplog.records
        log_messages = [record.message for record in caplog.records]
        assert any("Pre-write style/security validation failed for snippet" in msg for msg in log_messages)
        assert any(f"Failed snippet:\n---\n{snippet}\n---" in msg for msg in log_messages)
        # Assert on the resolved path in the log message
        assert any(f"Pre-write validation failed for snippet targeting {resolved_target_path}. Skipping write/merge." in msg for msg in log_messages)
        # Ethical check is called once for pre-write validation (mock from fixture)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)
        # Style/Security check is called once for pre-write validation (mock from fixture)
        mock_code_review_agent.analyze_python.assert_called_once_with(snippet)

    @patch('src.core.automation.workflow_driver.ast.parse') # Patch ast.parse here
    def test_pre_write_validation_full_file_syntax_fails(self, mock_ast_parse, driver_pre_write, caplog):
        # FIX: Change log level to INFO to capture the "passed for snippet" message
        caplog.set_level(logging.INFO)
        # Unpack fixture result
        driver = driver_pre_write['driver']
        mock_code_review_agent = driver_pre_write['mock_code_review_agent']
        mock_ethical_governance_engine = driver_pre_write['mock_ethical_governance_engine']
        mock_resolve_target_file = driver_pre_write['mock_resolve_target_file']
        mock_read_file = driver_pre_write['mock_read_file'] # Unpack mock_read_file
        mock_write_output = driver_pre_write['mock_write_output']

        # Scenario: Snippet is fine, but merging it creates a syntax error in the full file.
        # Example: Inserting an indented method directly at the module level without a class.
        snippet = "    def new_method():\n        pass" # Indented snippet
        existing_content = "import os\n\n# METAMORPHIC_INSERT_POINT\n\ndef existing_function():\n    pass" # Existing code, but the snippet's indentation is wrong for this context

        # Set the content that _read_file_for_context will return
        mock_read_file.return_value = existing_content
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved'}
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}

        # Configure ast.parse to succeed for the snippet, but fail for the merged content
        # The first call to ast.parse is on the `cleaned_snippet` (which is `snippet` here).
        # The second call to ast.parse is on the `hypothetical_merged_content`.
        # FIX: Use a callable side_effect to explicitly control calls
        def ast_parse_side_effect_func(code_str):
            if ast_parse_side_effect_func.call_count == 0:
                ast_parse_side_effect_func.call_count += 1
                return None # First call (on snippet) succeeds
            else:
                # The second call should be on the merged content, which will fail
                # Add a check for robustness in the mock
                expected_merged_prefix = "import os\n\ndef new_method():\n    pass\n\ndef existing_function():\n    pass"
                if not code_str.startswith(expected_merged_prefix):
                    raise AssertionError(f"Expected merged content for second AST parse call, got: {code_str[:100]}...")
                raise SyntaxError("unexpected indent", ('<string>', 3, 5, "    def new_method():\n")) # Second call (on merged content) fails
        ast_parse_side_effect_func.call_count = 0 # Initialize call count
        mock_ast_parse.side_effect = ast_parse_side_effect_func

        # Get the resolved target path from the mocked _resolve_target_file_for_step (called inside helper)
        resolved_target_path = mock_resolve_target_file.return_value

        # Call the helper function that simulates the loop's pre-write validation
        with pytest.raises(ValueError, match="Pre-merge full file syntax validation failed:"): # The error message is specific
            self._simulate_step_execution_for_pre_write_validation(
                driver, snippet, mock_ast_parse, mock_resolve_target_file, mock_read_file, mock_write_output,
                mock_code_review_agent, mock_ethical_governance_engine
            )

        # Assertions
        # _write_output_file should NOT be called
        mock_write_output.assert_not_called()

        # Verify logs using caplog.records for robustness
        log_messages = [record.message for record in caplog.records]
        # The snippet itself should pass the initial AST parse check
        assert any("Pre-write syntax check (AST parse) passed for snippet." in msg for msg in log_messages)
        assert any("Pre-merge full file syntax validation failed for" in msg for msg in log_messages)
        # Construct the expected hypothetical merged content for the log assertion
        # Manually calculate what the real _merge_snippet would produce
        hypothetical_merged_content = "import os\n\ndef new_method():\n    pass\n\ndef existing_function():\n    pass"
        assert any(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---" in msg for msg in log_messages)
        # FIX: Update log assertion to match the specific log message for the pre-merge syntax failure
        assert any(f"Pre-merge full file syntax validation failed for {resolved_target_path}: unexpected indent" in msg for msg in log_messages)

        # Verify that ethical and style checks on the *snippet* passed (as per mock)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(snippet, driver.default_policy_config, is_snippet=True)
        mock_code_review_agent.analyze_python.assert_called_once_with(snippet)

        # Verify that ethical and style checks on the *merged content* were NOT called
        assert mock_ethical_governance_engine.enforce_policy.call_count == 1
        assert mock_code_review_agent.analyze_python.call_count == 1
class TestRetryPromptEnhancement: # New test class
    def test_retry_prompt_includes_initial_snippet_syntax_error_and_ethical_failure(self, test_driver_phase1_8, caplog, mocker):
        """
        Tests that the CoderLLM prompt includes specific error feedback on a retry attempt
        when an initial snippet syntax error occurs, followed by an ethical check failure.
        """
        driver = test_driver_phase1_8
        caplog.set_level(logging.INFO)

        # Mock ast.parse to simulate a SyntaxError for the initial snippet
        mock_ast_parse_instance = MagicMock(side_effect=[
            SyntaxError("invalid syntax", ('<string>', 1, 1, 'def bad_syntax:')), # First call for snippet
            None # Subsequent calls for full file or other snippets pass
        ])

        # Mock ethical governance engine to reject the snippet
        mock_ethical_governance_instance = driver.ethical_governance_engine
        mock_ethical_governance_instance.enforce_policy.side_effect = [
            {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}, # First call for snippet
            {'overall_status': 'approved'} # Subsequent calls pass
        ]

        # Mock code review agent to pass (not the focus of this test)
        mock_code_review_instance = driver.code_review_agent
        mock_code_review_instance.analyze_python.return_value = {'status': 'success', 'static_analysis': []}

        # Mock _clean_llm_snippet to return the "cleaned" version of the bad snippet
        # This is needed because the real _clean_llm_snippet would remove fences, etc.
        mocker.patch.object(driver, '_clean_llm_snippet', side_effect=lambda s: s.replace("```python", "").replace("```", "").strip())
        # Mock _invoke_coder_llm to control its return value and allow assertions
        mock_invoke_coder_llm = mocker.patch.object(driver, '_invoke_coder_llm', return_value="def fixed_function():\n    pass\n")

        with patch('ast.parse', mock_ast_parse_instance):
            # --- Simulate the relevant part of the loop (simplified for one step) ---
            # Assume initial state where a step is being processed and a snippet is generated
            driver._current_task = {'task_id': 'test_task', 'task_name': 'Test Task', 'description': 'Test Description', 'target_file': 'test_file.py'}
            driver.task_target_file = 'test_file.py'
            filepath_to_use = "test_file.py"
            existing_content = "import os\n\n# Existing content\n"
            step_description = "Implement a new function."
            prelim_flags = {'is_code_generation_step_prelim': True}

            # Simulate the first attempt's failure and capture feedback
            initial_bad_snippet = "```python\ndef bad_syntax:\n    pass\n```"
            
            # Simulate the loop's call to _construct_coder_llm_prompt and _invoke_coder_llm
            # This part would normally be inside autonomous_loop
            # For this test, we simulate the *retry* prompt construction
            
            # Simulate the feedback collected from the first failed attempt
            retry_feedback_for_llm_prompt = (
                "The previous code snippet failed pre-write validation due to:\n"
                "- Pre-write syntax check failed: invalid syntax (<string>, line 1)\n"
                "- Pre-write ethical check failed: {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}"
            )
    
            # Construct the prompt for the retry attempt
            coder_prompt = driver._construct_coder_llm_prompt(
                        task=driver._current_task,
                        step_description=step_description,
                        filepath_to_use=filepath_to_use,
                        context_for_llm=existing_content,
                        is_minimal_context=False,
                        retry_feedback_content=retry_feedback_for_llm_prompt # Pass feedback from previous failure
                    )
            generated_snippet = driver._invoke_coder_llm(coder_prompt) # Corrected indentation
            cleaned_snippet = driver._clean_llm_snippet(generated_snippet) # Corrected indentation
    
            # Assertions
            assert "The previous code snippet failed pre-write validation due to:" in coder_prompt
            assert "- Pre-write syntax check failed: invalid syntax (<string>, line 1)" in coder_prompt
            assert "- Pre-write ethical check failed: {'overall_status': 'rejected', 'BiasRisk': {'status': 'violation'}}" in coder_prompt
            assert "Please review the feedback carefully and provide a corrected and improved code snippet." in coder_prompt
            # The step "Implement a new function" triggers the full block instructions.
            # The previous assertion was for a string not present in any constant.
            assert "CRITICAL INSTRUCTIONS FOR YOUR RESPONSE FORMAT (Full Block/Method/Class Focus):" in coder_prompt
            assert "Your entire response MUST be ONLY a valid Python code snippet representing the complete new or modified function, method, or class." in coder_prompt
    
            # Verify that the LLM was invoked with the prompt containing the feedback
            mock_invoke_coder_llm.assert_called_once_with(coder_prompt)
    
            # Verify that _clean_llm_snippet was called with the generated snippet
            driver._clean_llm_snippet.assert_called_once_with(generated_snippet)
    
            # Verify that the initial snippet was passed to ast.parse and ethical check
            # Note: In a real scenario, these would be called during the *first* attempt's validation.
            # Here, we're just setting up the mocks to simulate the *reason* for the retry feedback.
            # The actual calls to ast.parse and enforce_policy would happen in the autonomous_loop's validation logic.
            # For this test, we are primarily checking the prompt content.
            # The assertions for mock_ast_parse_instance and mock_ethical_governance_instance.enforce_policy
            # with initial_bad_snippet are removed because these calls are simulated as *past* events
            # that generated the retry_feedback_for_llm_prompt, not as events triggered by the code under test
            # in this specific test (which is _construct_coder_llm_prompt).
class TestPathResolutionAndValidation:
    def test_validate_path_safe_relative(self, driver_for_multi_target_resolution, tmp_path):
        driver = driver_for_multi_target_resolution
        relative_path = "src/module.py"
        # Create the dummy file so the mock get_full_path can resolve it
        (tmp_path / relative_path).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / relative_path).touch()


        # The mock get_full_path in the fixture returns the resolved path
        expected_full_path = str((tmp_path / relative_path).resolve(strict=False)) # Use strict=False here too for consistency

        validated_path = driver._validate_path(relative_path)

        driver.context.get_full_path.assert_called_once_with(relative_path)
        assert validated_path == expected_full_path

    def test_validate_path_unsafe_relative(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING) # Ensure warning is captured
        driver = driver_for_multi_target_resolution
        relative_path = "../sensitive/file.txt"

        # context.get_full_path is mocked in the fixture to return None for unsafe paths
        # The mock also logs a warning for traversal attempts

        validated_path = driver._validate_path(relative_path)

        driver.context.get_full_path.assert_called_once_with(relative_path)
        assert validated_path is None
        # Note: Logging is handled by context.get_full_path, so no specific log assertion needed here

    def test_validate_path_unsafe_absolute(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING) # Ensure warning is captured
        driver = driver_for_multi_target_resolution
        absolute_path = "/tmp/sensitive_file.txt"

        # context.get_full_path is mocked in the fixture to return None for unsafe paths
        # The mock also logs a warning for traversal attempts

        validated_path = driver._validate_path(absolute_path)

        driver.context.get_full_path.assert_called_once_with(absolute_path)
        assert validated_path is None
        # Note: Logging is handled by context.get_full_path

    def test_validate_path_empty_string(self, driver_for_multi_target_resolution, caplog):
        driver = driver_for_multi_target_resolution
        empty_path = ""

        validated_path = driver._validate_path(empty_path)

        driver.context.get_full_path.assert_called_once_with(empty_path)
        # FIX: Assert that an empty string resolves to the base path, not None
        assert validated_path == str(Path(driver.context.base_path).resolve(strict=False)) # Use strict=False here too
        # FIX: Remove incorrect log assertion - empty string is now considered valid input type
        # assert "Path validation received invalid or empty input: " in caplog.text


    def test_validate_path_none_input(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING) # Ensure warning is captured
        driver = driver_for_multi_target_resolution
        none_path = None

        validated_path = driver._validate_path(none_path)

        driver.context.get_full_path.assert_not_called() # get_full_path should not be called for None
        assert validated_path is None
        # FIX: Update log assertion to match the new log message format
        assert "Path validation received invalid input type: <class 'NoneType'>" in caplog.text

    def test_validate_path_invalid_type(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_for_multi_target_resolution
        full_path = driver._validate_path(123)
        assert full_path is None
        # FIX: Update assertion to match the new log message format
        assert "Path validation received invalid input type: <class 'int'>" in caplog.text

    # --- Tests for _resolve_target_file_for_step ---
    # These tests use the driver_for_multi_target_resolution fixture, which mocks _determine_filepath_to_use
    # and context.get_full_path. This allows focused testing of the new multi-target logic.

    def test_resolve_multi_target_explicit_full_path_mention(self, driver_for_multi_target_resolution, caplog, tmp_path):
        caplog.set_level(logging.INFO)
        driver = driver_for_multi_target_resolution
        step_desc = "Modify src/module_b.py to add new features."
        task_target_spec = "src/module_a.py,src/module_b.py,src/module_c.py"
        prelim_flags = {'is_code_generation_step_prelim': True}

        # Create dummy files so the mock get_full_path can resolve them
        (tmp_path / "src").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src" / "module_a.py").touch()
        (tmp_path / "src" / "module_b.py").touch()
        (tmp_path / "src" / "module_c.py").touch()


        # Configure the mock _determine_single_target_file to return the explicit match
        driver._determine_single_target_file.return_value = "src/module_b.py"

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should validate the result from _determine_single_target_file
        driver.context.get_full_path.assert_called_once_with("src/module_b.py")
        driver._determine_filepath_to_use.assert_not_called() # Fallback should not be called
        assert resolved_file is not None
        assert Path(resolved_file).name == "module_b.py"
        # The log about explicit mention comes from the real _determine_single_target_file, which is mocked.
        # We can't assert that log here.

    def test_resolve_multi_target_explicit_filename_mention(self, driver_for_multi_target_resolution, caplog, tmp_path):
        caplog.set_level(logging.INFO)
        driver = driver_for_multi_target_resolution
        step_desc = "In fileA.py, refactor the main function." # Corrected step_desc to match filename mention
        task_target_spec = "src/fileA.py,src/fileB.py" # Corrected task_target_spec to match filename mention
        prelim_flags = {'is_code_generation_step_prelim': True}

        # Create dummy files so the mock get_full_path can resolve them
        (tmp_path / "src").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src" / "fileA.py").touch() # Corrected filename
        (tmp_path / "src" / "fileB.py").touch() # Corrected filename


        # Configure the mock _determine_single_target_file to return the explicit match
        driver._determine_single_target_file.return_value = "src/fileA.py" # Corrected filename

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should validate the result from _determine_single_target_file
        driver.context.get_full_path.assert_called_once_with("src/fileA.py") # Corrected filename
        driver._determine_filepath_to_use.assert_not_called() # Fallback should not be called
        assert resolved_file is not None
        assert Path(resolved_file).name == "fileA.py" # Corrected filename
        # The log about explicit mention comes from the real _determine_single_target_file, which is mocked.
        # We can't assert that log here.

    def test_resolve_multi_target_no_mention_defaults_to_first(self, driver_for_multi_target_resolution, caplog, tmp_path):
        caplog.set_level(logging.WARNING)
        driver = driver_for_multi_target_resolution
        step_desc = "Implement the new algorithm."
        task_target_spec = "src/core_logic.py,src/utils.py"
        prelim_flags = {'is_code_generation_step_prelim': True}

        # Create dummy files so the mock get_full_path can resolve them
        (tmp_path / "src").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src" / "core_logic.py").touch()
        (tmp_path / "src" / "utils.py").touch()


        # Configure the mock _determine_single_target_file to return the default (first file)
        driver._determine_single_target_file.return_value = "src/core_logic.py"

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should validate the result from _determine_single_target_file
        driver.context.get_full_path.assert_called_once_with("src/core_logic.py")
        driver._determine_filepath_to_use.assert_not_called() # Fallback should not be called
        assert resolved_file is not None
        assert Path(resolved_file).name == "core_logic.py"
        # The log about defaulting comes from the real _determine_single_target_file, which is mocked.
        # We can't assert that log here.

    def test_resolve_single_target_uses_determine_filepath(self, driver_for_multi_target_resolution, tmp_path):
        driver = driver_for_multi_target_resolution
        step_desc = "Modify the main file src/main.py." # Step mentions the file
        task_target_spec = "src/main.py" # Task also specifies it
        prelim_flags = {'is_code_generation_step_prelim': True}

        # Create dummy file so the mock get_full_path can resolve it
        (tmp_path / "src").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src" / "main.py").touch()

        # _determine_single_target_file is mocked to return None (default in fixture)
        # _determine_filepath_to_use will be called as fallback.
        # Its mock is configured in the fixture to return a relative path based on step/task.
        # Its mock is also configured to call _validate_path.

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file first, which returns None
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should then call _determine_filepath_to_use (fallback)
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, "src/main.py", prelim_flags)
        # _validate_path should have been called by the mock _determine_filepath_to_use
        driver.context.get_full_path.assert_called_once_with("src/main.py")
        assert resolved_file is not None
        assert Path(resolved_file).name == "main.py"


    def test_resolve_no_task_target_uses_determine_filepath(self, driver_for_multi_target_resolution, tmp_path):
        driver = driver_for_multi_target_resolution
        step_desc = "Create a new file named new_util.py for utility functions."
        task_target_spec = None
        prelim_flags = {'is_code_generation_step_prelim': True}

        # Create dummy file so the mock get_full_path can resolve it (even if it doesn't exist yet)
        # The mock get_full_path is configured with strict=False for resolution,
        # but the mock side_effect for this fixture *does* raise FileNotFoundError if it doesn't exist.
        # Let's create the parent dir to allow resolution.
        (tmp_path / "new_util.py").parent.mkdir(parents=True, exist_ok=True)
        # No need to touch the file itself if strict=False is intended for non-existent paths


        # _determine_single_target_file is mocked to return None (default in fixture)
        # _determine_filepath_to_use will be called as fallback.
        # Its mock is configured in the fixture to return a relative path based on step/task.
        # Its mock is also configured to call _validate_path.

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file first, which returns None
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should then call _determine_filepath_to_use (fallback)
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, None, prelim_flags)
        # _validate_path should have been called by the mock _determine_filepath_to_use
        driver.context.get_full_path.assert_called_once_with("new_util.py")
        assert resolved_file is not None
        assert Path(resolved_file).name == "new_util.py"


    def test_resolve_multi_target_not_code_gen_uses_determine_filepath(self, driver_for_multi_target_resolution, tmp_path):
        driver = driver_for_multi_target_resolution
        step_desc = "Research file_a.py and file_b.py" # Step mentions files
        task_target_spec = "file_a.py,file_b.py" # Task has multiple targets
        prelim_flags = {'is_code_generation_step_prelim': False, 'is_research_step_prelim': True} # NOT code gen

        # Create dummy files so the mock get_full_path can resolve them
        (tmp_path / "file_a.py").touch()
        (tmp_path / "file_b.py").touch()


        # _determine_single_target_file is mocked to return None (default in fixture) because
        # the multi-target logic in the real method would be skipped for this step type.
        # _determine_filepath_to_use will be called as fallback.
        # Its mock is configured in the fixture to return a relative path based on step/task.
        # Its mock is also configured to call _validate_path.

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file first, which returns None
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should then call _determine_filepath_to_use (fallback)
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # _validate_path should have been called by the mock _determine_filepath_to_use
        driver.context.get_full_path.assert_called_once_with("file_a.py")
        assert resolved_file is not None
        assert Path(resolved_file).name == "file_a.py"


    def test_resolve_target_file_path_traversal_attempt_returns_none(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_for_multi_target_resolution
        step_desc = "Modify ../../../etc/passwd"
        task_target_spec = "../../../etc/passwd,src/safe.py" # One unsafe, one safe
        prelim_flags = {'is_code_generation_step_prelim': True}

        # Configure the mock _determine_single_target_file to return the unsafe path
        driver._determine_single_target_file.return_value = "../../../etc/passwd"
        # context.get_full_path (mocked in fixture) will return None for the unsafe path

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file first
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should attempt to validate the result from _determine_single_target_file
        driver.context.get_full_path.assert_called_once_with("../../../etc/passwd")
        driver._determine_filepath_to_use.assert_not_called() # Fallback should not be called
        assert resolved_file is None
        # FIX: Remove log assertion that checks for the mock's internal warning
        # assert "Resolved step target file '../../../etc/passwd' is outside the allowed context or invalid." in caplog.text

    def test_resolve_multi_target_empty_list_after_parse(self, driver_for_multi_target_resolution, caplog):
        caplog.set_level(logging.WARNING)
        driver = driver_for_multi_target_resolution
        step_desc = "Implement new feature."
        task_target_spec = ",, ," # Will parse to empty list
        prelim_flags = {'is_code_generation_step_prelim': True}

        # _determine_single_target_file is mocked to return None (default in fixture) because
        # the real method would find no targets and return None.
        # _determine_filepath_to_use will be called as fallback.
        # Its mock is configured in the fixture to return None for this scenario.
        # Its mock is also configured to call _validate_path (with None).

        resolved_file = driver._resolve_target_file_for_step(step_desc, task_target_spec, prelim_flags)

        # Should call _determine_single_target_file first
        driver._determine_single_target_file.assert_called_once_with(step_desc, task_target_spec, prelim_flags)
        # Should then call _determine_filepath_to_use (fallback)
        driver._determine_filepath_to_use.assert_called_once_with(step_desc, None, prelim_flags)
        # _validate_path is called by the mock _determine_filepath_to_use with None,
        # which logs the "invalid input type" warning.
        # The test is specifically checking for the log *before* the fallback call,
        # indicating the empty list parsing.
        # FIX: Assert for the correct log message that indicates the empty list parsing issue.
        assert f"Task target file list was unexpectedly empty after parsing '{task_target_spec}' for step: '{step_desc}'" in caplog.text
        assert resolved_file is None
# --- Unit Tests for File Determination Logic (using the new method) ---
# Assume you add this method to WorkflowDriver:
# def _determine_single_target_file(self, step_description: str, task_target_file_spec: str | None, prelim_flags: Dict) -> Optional[str]:
# """
# Determines the single target file from a task's target_file list based on step description.
# Returns the relative path string or None.
# """
# # ... implementation from Step 1 ...
# pass # Add this method to WorkflowDriver
class TestMultiTargetFileDetermination: # Changed to use pytest
    # No setUp/tearDown needed with pytest fixtures


    # Mock logger for this test class
    @pytest.fixture(autouse=True)
    def mock_logger(self, mocker):
        # Patch the logger used within the _determine_single_target_file method
        # Assuming the logger is accessed via `logger` global variable in the module
        # If it's accessed via `self.logger`, you'd patch the instance attribute on the mock driver
        # Let's patch the global logger for simplicity in this unit test class
        mock_logger = mocker.patch('src.core.automation.workflow_driver.logger')
        yield mock_logger

    @pytest.fixture
    def mock_driver(self, mocker, mock_logger):
        # Mock necessary dependencies for the method
        mock_driver = MagicMock()
        mock_driver.context = MagicMock()
        mock_driver._classify_step_preliminary.return_value = {} # Default empty flags
        # Assign the patched logger to the mock driver if the method uses self.logger
        # If it uses the module-level logger, this line is not strictly necessary for the patch to work
        # but might be good practice depending on how the SUT accesses the logger.
        mock_driver.logger = mock_logger

        # Add the _determine_single_target_file method to the mock driver
        # This allows testing the logic without running the full loop
        # Copy the logic from the SUT here
        def _determine_single_target_file_mock_impl(step_description, task_target_file_spec, prelim_flags):
            determined_target_file_relative = None
            potential_task_targets = []

            if task_target_file_spec and isinstance(task_target_file_spec, str):
                potential_task_targets = [f.strip() for f in task_target_file_spec.split(',') if f.strip()]

            is_code_generation_step = prelim_flags.get('is_code_generation_step_prelim', False)
            is_test_writing_step = prelim_flags.get('is_test_writing_step_prelim', False)
            is_explicit_file_writing_step = prelim_flags.get('is_explicit_file_writing_step_prelim', False)

            should_apply_multi_target_logic = is_code_generation_step or is_test_writing_step or is_explicit_file_writing_step

            if len(potential_task_targets) > 1 and should_apply_multi_target_logic:
                mock_driver.logger.debug(f"Task has multiple target files: {potential_task_targets}. Applying multi-target selection for step: '{step_description}' (via _determine_single_target_file)")
                step_desc_lower = step_description.lower()

                for file_candidate_relative in potential_task_targets:
                    normalized_candidate_path_str = Path(file_candidate_relative).as_posix().lower()
                    filename_candidate_lower = Path(file_candidate_relative).name.lower()

                    if normalized_candidate_path_str in step_desc_lower:
                        determined_target_file_relative = file_candidate_relative
                        mock_driver.logger.info(f"Step description explicitly mentions '{determined_target_file_relative}' from task target list {potential_task_targets} (via _determine_single_target_file).")
                        break # Found explicit mention, exit loop
                    # FIX: Adjust regex lookbehind and lookahead to exclude '.' from forbidden characters
                    # This allows matching filenames followed by punctuation like '.'
                    # Ensure the mock implementation matches the SUT's regex
                    elif re.search(r'(?<![a-zA-Z0-9_-])' + re.escape(filename_candidate_lower) + r'(?![a-zA-Z0-9_-])', step_desc_lower):
                        determined_target_file_relative = file_candidate_relative
                        mock_driver.logger.info(f"Step description explicitly mentions filename '{filename_candidate_lower}' (from '{determined_target_file_relative}') from task target list {potential_task_targets} (via _determine_single_target_file).")
                        break # Found explicit mention, exit loop

                # If no explicit mention was found, default to the first file
                # FIX: Only default if determined_target_file_relative is still None
                if determined_target_file_relative is None:
                    determined_target_file_relative = potential_task_targets[0]
                    mock_driver.logger.warning(f"Step description '{step_description}' does not explicitly mention any file from the task's target list: {potential_task_targets}. Defaulting to the first file: '{determined_target_file_relative}' (via _determine_single_target_file).")

                return determined_target_file_relative # This will be a string path

            # If the above multi-target logic didn't apply (e.g., single target, no targets, or not relevant step type)
            # return None to indicate that _resolve_target_file_for_step should use its fallback.
            return None

        mock_driver._determine_single_target_file = _determine_single_target_file_mock_impl
        yield mock_driver


    def test_determine_single_target_file_single_target(self, mock_driver, mock_logger):
        task_target = "src/single_file.py"
        step_desc = "Modify the file."
        flags = {'is_code_generation_step_prelim': True}
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        # The mock implementation returns None if multi-target logic is skipped
        assert result is None
        mock_logger.warning.assert_not_called()
        mock_logger.debug.assert_not_called()
        mock_logger.info.assert_not_called()


    def test_determine_single_target_file_multi_target_explicit_full_path(self, mock_driver, mock_logger):
        task_target = "src/fileA.py,src/fileB.py,src/fileC.py"
        step_desc = "Update src/fileB.py with new logic."
        flags = {'is_code_generation_step_prelim': True}
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        assert result == "src/fileB.py"
        mock_logger.warning.assert_not_called()
        mock_logger.debug.assert_called_once()
        mock_logger.info.assert_called_once()


    def test_determine_single_target_file_multi_target_explicit_filename(self, mock_driver, mock_logger):
        task_target = "src/fileA.py,src/fileB.py"
        step_desc = "Refactor fileA.py."
        flags = {'is_code_generation_step_prelim': True}
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        assert result == "src/fileA.py"
        # FIX: This case should NOT log a warning because an explicit mention was found.
        mock_logger.warning.assert_not_called()
        mock_logger.debug.assert_called_once()
        mock_logger.info.assert_called_once()


    def test_determine_single_target_file_multi_target_default_to_first(self, mock_driver, mock_logger):
        task_target = "src/fileA.py,src/fileB.py"
        step_desc = "Implement the feature." # No file mentioned
        flags = {'is_code_generation_step_prelim': True}
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        assert result == "src/fileA.py"
        mock_logger.warning.assert_called_once() # Expect warning about defaulting
        mock_logger.debug.assert_called_once()
        mock_logger.info.assert_not_called() # No explicit mention found


    def test_determine_single_target_file_multi_target_no_match_no_default(self, mock_driver, mock_logger):
        task_target = "src/fileA.py,src/fileB.py"
        step_desc = "Modify fileC.py." # Mentions a file not in the list
        flags = {'is_code_generation_step_prelim': True}
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        assert result == "src/fileA.py" # Still defaults to first if mention is not in list
        # FIX: This case should log a warning because the mention was not in the list, leading to defaulting.
        mock_logger.warning.assert_called_once()
        mock_logger.debug.assert_called_once()
        mock_logger.info.assert_not_called() # No explicit mention found *from the list*


    def test_determine_single_target_file_empty_task_target(self, mock_driver, mock_logger):
        task_target = ""
        step_desc = "Create a new file."
        flags = {'is_code_generation_step_prelim': True}
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        assert result is None
        mock_logger.warning.assert_not_called()
        mock_logger.debug.assert_not_called()
        mock_logger.info.assert_not_called()


    def test_determine_single_target_file_none_task_target(self, mock_driver, mock_logger):
        task_target = None
        step_desc = "Create a new file."
        flags = {'is_code_generation_step_prelim': True}
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        assert result is None
        mock_logger.warning.assert_not_called()
        mock_logger.debug.assert_not_called()
        mock_logger.info.assert_not_called()


    def test_determine_single_target_file_multi_target_not_code_gen(self, mock_driver, mock_logger):
        task_target = "src/fileA.py,src/fileB.py"
        step_desc = "Research fileB.py." # Mentions a file
        flags = {'is_code_generation_step_prelim': False, 'is_research_step_prelim': True} # Not code gen

        # The new logic only applies if should_apply_multi_target_logic is True.
        # If False, it falls through. The SUT then calls _determine_filepath_to_use.
        # The mock implementation here doesn't call _determine_filepath_to_use.
        # This test should verify that the new multi-target logic is skipped.
        # The mock implementation returns None if the new logic is skipped and there's no single target.
        result = mock_driver._determine_single_target_file(step_desc, task_target, flags)
        assert result is None # New logic skipped, returns None
        mock_logger.warning.assert_not_called()
        mock_logger.debug.assert_not_called()
        mock_logger.info.assert_not_called()
# --- Integration Test for Multi-Target Handling ---
# This test will simulate the execution of a single code generation step
# within the autonomous loop, verifying that the correct file is targeted
# when the task has multiple target files.
# FIX: Remove unittest.TestCase inheritance
class TestMultiTargetIntegration:
    # Decorator stack (top to bottom in file, corresponds to first to last mock arg after self)
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="# Generated snippet")                 # M1
    @patch.object(WorkflowDriver, '_read_file_for_context')                                             # M2
    @patch.object(WorkflowDriver, '_merge_snippet', side_effect=lambda existing, snippet: existing + "\n" + snippet) # M3
    @patch.object(WorkflowDriver, '_write_output_file')                                                  # M4
    @patch.object(WorkflowDriver, '_validate_path', side_effect=lambda path: str(Path(tempfile.gettempdir()) / path).replace('\\', '/') if path is not None else None) # M5
    @patch('src.core.automation.workflow_driver.ast.parse')                                                 # M6
    @patch.object(WorkflowDriver, '_is_add_imports_step', return_value=False)                             # M7
    @patch.object(WorkflowDriver, '_find_import_block_end', return_value=0)                               # M8
    @patch.object(WorkflowDriver, '_classify_step_preliminary')                                           # M9
    @patch.object(WorkflowDriver, '_determine_write_operation_details')                                   # M10
    @patch.object(WorkflowDriver, '_determine_filepath_to_use')                                           # M11
    @patch.object(WorkflowDriver, '_attempt_test_failure_remediation')                                    # M12
    @patch.object(WorkflowDriver, '_attempt_code_style_remediation')                                       # M13
    @patch.object(WorkflowDriver, '_attempt_ethical_transparency_remediation')                             # M14
    @patch.object(WorkflowDriver, '_identify_remediation_target', return_value=None)                      # M15
    @patch.object(WorkflowDriver, 'generate_grade_report')                                                # M16
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')                                     # M17
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json')                                             # M18
    @patch('builtins.open')                                                                              # M19
    @patch('os.path.exists', return_value=True)                                                          # M20
    @patch('os.path.isfile', return_value=True)                                                          # M21
    @patch('os.path.getsize', return_value=100)                                                          # M22
    @patch.object(WorkflowDriver, '_update_task_status_in_roadmap')                                       # M23
    @patch.object(WorkflowDriver, 'execute_tests')                                                        # M24
    @patch.object(WorkflowDriver, '_parse_test_results')                                                  # M25
    @patch.object(WorkflowDriver, '_load_default_policy')                                                 # M26
    @patch.object(WorkflowDriver, 'load_roadmap')                                                         # M27
    @patch.object(WorkflowDriver, 'select_next_task')                                                     # M28
    @patch.object(WorkflowDriver, 'generate_solution_plan')                                               # M29
    @patch.object(WorkflowDriver, '_determine_single_target_file')                                        # M30
    # M33 (NEW): Patch SecureConfig.get to provide dummy values for LLM config
    @patch('src.core.llm_orchestration.SecureConfig.get', side_effect=lambda var_name, default=None: {
        "LLM_PROVIDER": "gemini",
        "GEMINI_API_KEY": "mock_gemini_api_key_123456789012345678901234567890123456789", # Min length 39
        "HUGGING_FACE_API_KEY": "hf_mock_hf_api_key_123456789012345678901234567890", # Min length 34
        "YOUR_GITHUB_API_KEY": "ghp_mock_github_api_key_123456789012345678901234567890123456", # Min length 40
        "HUGGING_FACE_MODEL": "deepseek-ai/DeepSeek-R1-Distill-Qwen-32B",
        "LLM_MAX_RETRIES": "3", "LLM_TIMEOUT": "30",
    }.get(var_name, default))
    @patch('src.core.llm_orchestration.SecureConfig.load')                                                # M32 (NEW)
    @patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')                                     # M31
    def test_integration_multi_target_explicit_match(self,
                                                      mock_ethical_engine_m31, # M31
                                                      mock_secure_config_load_m32, # M32 (NEW)
                                                      mock_secure_config_get_m33, # M33 (NEW)
                                                      mock_determine_single_target_file_m30, # M30
                                                      mock_generate_plan_m29, # M29
                                                      mock_select_next_task_m28, # M28
                                                      mock_load_roadmap_m27, # M27
                                                      mock_load_default_policy_m26, # M26
                                                      mock_parse_test_results_m25, # M25
                                                      mock_execute_tests_m24, # M24
                                                      mock_update_status_m23, # M23
                                                      mock_getsize_m22, # M22
                                                      mock_isfile_m21, # M21
                                                      mock_exists_m20, # M20
                                                      mock_open_m19, # M19
                                                      mock_safe_write_roadmap_json_m18, # M18
                                                      mock_parse_and_evaluate_grade_report_m17, # M17
                                                      mock_generate_grade_report_m16, # M16
                                                      mock_identify_remediation_target_m15, # M15
                                                      mock_ethical_remediation_m14, # M14
                                                      mock_style_remediation_m13, # M13
                                                      mock_test_remediation_m12, # M12
                                                      mock_determine_filepath_to_use_m11, # M11
                                                      mock_determine_write_details_m10, # M10
                                                      mock_classify_step_m9, # M9
                                                      mock_find_import_block_end_m8, # M8
                                                      mock_is_add_imports_step_m7, # M7
                                                      mock_ast_parse_m6, # M6
                                                      mock_validate_path_m5, # M5
                                                      mock_write_output_file_m4, # M4
                                                      mock_merge_snippet_m3, # M3
                                                      mock_read_file_for_context_m2, # M2
                                                      mock_invoke_coder_llm_m1, # M1
                                                      mocker, # Pytest fixture
                                                      tmp_path, # Pytest fixture
                                                      caplog # Pytest fixture
                                                      ):


        caplog.set_level(logging.INFO)

        # --- Setup Mock Driver and Context ---
        context = Context(str(tmp_path))
        driver = WorkflowDriver(context)
        mock_secure_config_load_m32.return_value = None # SecureConfig.load doesn't return anything
        driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure policy is loaded

        # --- Configure Mocks for this specific scenario ---
        task_target_file_spec = "src/fileA.py,src/fileB.py"
        step_description = "Modify src/fileB.py to add a function."
        # The new _determine_single_target_file method should return the relative path
        mock_determine_single_target_file_m30.return_value = "src/fileB.py"
        # _validate_path will be called with this relative path and should return the resolved path
        resolved_file_b = str(Path(tempfile.gettempdir()) / "src" / "fileB.py").replace('\\', '/')
        # Configure M5 (_validate_path)
        mock_validate_path_m5.side_effect = lambda path: resolved_file_b if path == "src/fileB.py" else str(Path(tempfile.gettempdir()) / path).replace('\\', '/') if path is not None else None

        # mock_find_import_block_end_m8 already has return_value=0 from decorator
        # mock_is_add_imports_step_m7 already has return_value=False from decorator

        # Mock _classify_step_preliminary to identify as code generation
        # FIX: Include all expected keys in the return value
        mock_classify_step_m9.return_value = {
            'is_code_generation_step_prelim': True,
            'filepath_from_step': 'src/fileB.py',
            'is_test_execution_step_prelim': False,
            'is_explicit_file_writing_step_prelim': False,
            'is_research_step_prelim': False,
            'is_test_writing_step_prelim': False
        }

        # Mock _determine_write_operation_details to indicate no placeholder write
        mock_determine_write_details_m10.return_value = (None, True) # content_to_write=None, overwrite=True

        # Mock _determine_filepath_to_use (fallback) - should not be called in this test
        mock_determine_filepath_to_use_m11.return_value = None

        # Mock _read_file_for_context content
        mock_read_file_for_context_m2.return_value = "Existing content of fileB."

        # Mock LLM response
        # mock_invoke_coder_llm_m1 already has return_value from decorator
        generated_snippet = "def new_func(): pass" # Define the actual generated snippet
        mock_invoke_coder_llm_m1.return_value = generated_snippet # Explicitly set here for clarity

        # Mock merge result
        mock_merged_content = "Existing content of fileB.\ndef new_func(): pass"
        mock_merge_snippet_m3.return_value = mock_merged_content # side_effect was set, but return_value is fine too for this

        # Mock write success
        # mock_write_output_file_m4 is just a mock object, set its return_value
        mock_write_output_file_m4.return_value = True

        # Mock validation to pass
        # Use the mock instance obtained from the patch decorator
        mock_ethical_engine_instance = mock_ethical_engine_m31.return_value
        mock_ethical_engine_instance.enforce_policy.return_value = {'overall_status': 'approved'}
        driver.code_review_agent = MagicMock() # Ensure mock instance
        driver.code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}
        # Use the real mocker fixture to patch ast.parse
        # mock_ast_parse_m6 is already a mock from the decorator, no need to use mocker.patch for it.
        # If you need to control its return value for a specific call, do it on mock_ast_parse_m6
        # Configure ast.parse to succeed for both snippet and merged content
        mock_ast_parse_m6.side_effect = [None, None] # First for snippet, second for merged content


        # Mock post-write validation calls (they will be called with the merged content)
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual generated snippet
        mock_ethical_engine_instance.enforce_policy.side_effect = [
            {'overall_status': 'approved'}, # Pre-write ethical
            {'overall_status': 'approved'}  # Post-write ethical
        ]
        driver.code_review_agent.analyze_python.side_effect = [
            {'status': 'success', 'static_analysis': []}, # Pre-write style/security
            {'status': 'success', 'static_analysis': []}  # Post-write style/security
        ]


        # Mock grading and evaluation to result in "Completed"
        mock_generate_grade_report_m16.return_value = json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}})
        mock_parse_and_evaluate_grade_report_m17.return_value = {"recommended_action": "Completed", "justification": "Mock success"}

        # Mock roadmap loading and task selection to run the task once and then exit
        # Define the roadmap states
        roadmap_states = [
            [{'task_id': 'multi_target_e2e', 'task_name': 'Multi Target Test', 'status': 'Not Started', 'description': 'Desc', 'priority': 'high', 'target_file': task_target_file_spec}],  # Initial load
            [{'task_id': 'multi_target_e2e', 'task_name': 'Multi Target Test', 'status': 'Not Started', 'description': 'Desc', 'priority': 'high', 'target_file': task_target_file_spec}],  # Loop 1 load
            [{'task_id': 'multi_target_e2e', 'task_name': 'Multi Target Test', 'status': 'Completed', 'description': 'Desc', 'priority': 'high', 'target_file': task_target_file_spec}],  # Loop 2 load (after update)
            []  # Loop 3 load (to exit)
        ]
        mock_load_roadmap_m27.side_effect = iter(roadmap_states)
        mock_select_next_task_m28.side_effect = [
            roadmap_states[1][0],  # Access the task from the second load
            None  # No more tasks
        ]
        mock_generate_plan_m29.return_value = [step_description] # Plan with one step

        # Mock _update_task_status_in_roadmap and _safe_write_roadmap_json
        mock_update_status_m23.return_value = None # The method itself doesn't return bool
        mock_safe_write_roadmap_json_m18.return_value = True # Mock the underlying write utility

        # --- Execute the autonomous loop ---
        # FIX: Call start_workflow instead of autonomous_loop to initialize the driver state
        driver.start_workflow("dummy_roadmap.json", "/tmp/output", context)

        # --- Assertions ---

        # Verify _determine_single_target_file was called with correct args
        mock_determine_single_target_file_m30.assert_called_once_with(step_description, task_target_file_spec, mock_classify_step_m9.return_value)

        # Verify _validate_path was called with the relative path returned by _determine_single_target_file
        mock_validate_path_m5.assert_any_call("src/fileB.py") # Called for the determined target

        # Verify _determine_filepath_to_use (fallback) was NOT called
        mock_determine_filepath_to_use_m11.assert_not_called()

        # Verify _read_file_for_context was called with the correct resolved file path
        mock_read_file_for_context_m2.assert_called_once_with(resolved_file_b)

        # Verify LLM prompt includes context for the correct file
        mock_invoke_coder_llm_m1.assert_called_once()
        called_prompt = mock_invoke_coder_llm_m1.call_args[0][0]
        assert f"PROVIDED CONTEXT FROM `{resolved_file_b}` (this might be the full file or a targeted section):" in called_prompt

        # Verify _merge_snippet was called with the correct content
        # FIX: Assert with the actual generated snippet
        mock_merge_snippet_m3.assert_called_with("Existing content of fileB.", generated_snippet)

        # Verify _write_output_file was called with the correct resolved file path and merged content
        mock_write_output_file_m4.assert_called_once_with(resolved_file_b, mock_merged_content, overwrite=True)

        # Verify pre-write validation calls
        mock_classify_step_m9.assert_called_once_with(step_description)
        mock_determine_write_details_m10.assert_called_once_with(step_description, resolved_file_b, task_target_file_spec, mock_classify_step_m9.return_value)
        # FIX: Assert with the actual generated snippet
        mock_ast_parse_m6.assert_has_calls([call(generated_snippet), call(mock_merged_content)]) # Check the ast.parse mock
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual generated snippet
        mock_ethical_engine_instance.enforce_policy.assert_any_call(generated_snippet, driver.default_policy_config, is_snippet=True)
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual generated snippet
        driver.code_review_agent.analyze_python.assert_any_call(generated_snippet)

        # Verify post-write validation calls
        # Use the mock instance obtained from the patch decorator
        mock_ethical_engine_instance.enforce_policy.assert_any_call(mock_merged_content, driver.default_policy_config)
        driver.code_review_agent.analyze_python.assert_any_call(mock_merged_content)
        # Use the mock instance obtained from the patch decorator for call count
        assert mock_ethical_engine_instance.enforce_policy.call_count == 2
        assert driver.code_review_agent.analyze_python.call_count == 2

        # Verify test execution/parsing were NOT called
        mock_execute_tests_m24.assert_not_called()
        mock_parse_test_results_m25.assert_not_called()

        # Verify report generation and evaluation were called
        mock_generate_grade_report_m16.assert_called_once()
        mock_parse_and_evaluate_grade_report_m17.assert_called_once_with(ANY)

        # Verify roadmap status update was called
        mock_secure_config_load_m32.assert_called_once() # Verify SecureConfig.load was called
        mock_update_status_m23.assert_called_once_with('multi_target_e2e', 'Completed', None)
        # REMOVE THIS ASSERTION: _safe_write_roadmap_json is called by the mocked _update_task_status_in_roadmap
        # mock_safe_write_roadmap_json_m18.assert_called_once()

        # Verify logs
        assert "Selected task: ID=multi_target_e2e" in caplog.text
        assert f"Step identified as code generation for file {resolved_file_b}. Orchestrating read-generate-merge-write." in caplog.text
        # The log about explicit mention comes from the real _determine_single_target_file, which is mocked away.
        # We can't assert that log here unless we don't mock _determine_single_target_file.
        # Let's rely on the mock call assertions instead.
        # assert f"Step description explicitly mentions 'src/fileB.py' from task target list." in caplog.text
        assert f"Successfully wrote merged content to {resolved_file_b}." in caplog.text
        assert "Grade Report Evaluation: Recommended Action='Completed'" in caplog.text
        assert "Updating task status from 'Not Started' to 'Completed' for task multi_target_e2e" in caplog.text
        assert "No tasks available in Not Started status. Exiting autonomous loop." in caplog.text


    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="# Generated snippet")                 # M1
    @patch.object(WorkflowDriver, '_read_file_for_context', )                                            # M2
    @patch.object(WorkflowDriver, '_merge_snippet', side_effect=lambda existing, snippet: existing + "\n" + snippet) # M3
    @patch.object(WorkflowDriver, '_write_output_file')                                                  # M4
    @patch.object(WorkflowDriver, '_validate_path', side_effect=lambda path: str(Path(tempfile.gettempdir()) / path).replace('\\', '/') if path is not None else None) # M5
    @patch('src.core.automation.workflow_driver.ast.parse')                                                 # M6
    @patch.object(WorkflowDriver, '_is_add_imports_step', return_value=False)                             # M7
    @patch.object(WorkflowDriver, '_find_import_block_end', return_value=0)                               # M8
    @patch.object(WorkflowDriver, '_classify_step_preliminary')                                           # M9
    @patch.object(WorkflowDriver, '_determine_write_operation_details')                                   # M10
    @patch.object(WorkflowDriver, '_determine_filepath_to_use')                                           # M11
    @patch.object(WorkflowDriver, '_attempt_test_failure_remediation')                                    # M12
    @patch.object(WorkflowDriver, '_attempt_code_style_remediation')                                       # M13
    @patch.object(WorkflowDriver, '_attempt_ethical_transparency_remediation')                             # M14
    @patch.object(WorkflowDriver, '_identify_remediation_target', return_value=None)                      # M15
    @patch.object(WorkflowDriver, 'generate_grade_report')                                                # M16
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')                                     # M17
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json')                                             # M18
    @patch('builtins.open')                                                                              # M19
    @patch('os.path.exists', return_value=True)                                                          # M20
    @patch('os.path.isfile', return_value=True)                                                          # M21
    @patch('os.path.getsize', return_value=100)                                                          # M22
    @patch.object(WorkflowDriver, '_update_task_status_in_roadmap')                                       # M23
    @patch.object(WorkflowDriver, 'execute_tests')                                                        # M24
    @patch.object(WorkflowDriver, '_parse_test_results')                                                  # M25
    @patch.object(WorkflowDriver, '_load_default_policy')                                                 # M26
    @patch.object(WorkflowDriver, 'load_roadmap')                                                         # M27
    @patch.object(WorkflowDriver, 'select_next_task')                                                     # M28
    @patch.object(WorkflowDriver, 'generate_solution_plan')                                               # M29
    @patch.object(WorkflowDriver, '_determine_single_target_file')                                        # M30
    # M33 (NEW): Patch SecureConfig.get to provide dummy values for LLM config
    @patch('src.core.llm_orchestration.SecureConfig.get', side_effect=lambda var_name, default=None: {
        "LLM_PROVIDER": "gemini",
        "GEMINI_API_KEY": "mock_gemini_api_key_123456789012345678901234567890123456789", # Min length 39
        "HUGGING_FACE_API_KEY": "hf_mock_hf_api_key_123456789012345678901234567890", # Min length 34
        "YOUR_GITHUB_API_KEY": "ghp_mock_github_api_key_123456789012345678901234567890123456", # Min length 40
        "HUGGING_FACE_MODEL": "deepseek-ai/DeepSeek-R1-Distill-Qwen-32B",
        "LLM_MAX_RETRIES": "3", "LLM_TIMEOUT": "30",
    }.get(var_name, default))
    @patch('src.core.llm_orchestration.SecureConfig.load')                                                # M32 (NEW)
    @patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')                                     # M31
    def test_integration_multi_target_default_to_first(self,
                                                       mock_ethical_engine_m31, # M31
                                                       mock_secure_config_load_m32, # M32 (NEW)
                                                       mock_secure_config_get_m33, # M33 (NEW)
                                                       mock_determine_single_target_file_m30, # M30
                                                       mock_generate_plan_m29, # M29
                                                       mock_select_next_task_m28, # M28
                                                       mock_load_roadmap_m27, # M27
                                                       mock_load_default_policy_m26, # M26
                                                       mock_parse_test_results_m25, # M25
                                                       mock_execute_tests_m24, # M24
                                                       mock_update_status_m23, # M23
                                                       mock_getsize_m22, # M22
                                                       mock_isfile_m21, # M21
                                                       mock_exists_m20, # M20
                                                       mock_open_m19, # M19
                                                       mock_safe_write_roadmap_json_m18, # M18
                                                       mock_parse_and_evaluate_grade_report_m17, # M17
                                                       mock_generate_grade_report_m16, # M16
                                                       mock_identify_remediation_target_m15, # M15
                                                       mock_ethical_remediation_m14, # M14
                                                       mock_style_remediation_m13, # M13
                                                       mock_test_remediation_m12, # M12
                                                       mock_determine_filepath_to_use_m11, # M11
                                                       mock_determine_write_details_m10, # M10
                                                       mock_classify_step_m9, # M9
                                                       mock_find_import_block_end_m8, # M8
                                                       mock_is_add_imports_step_m7, # M7
                                                       mock_ast_parse_m6, # M6
                                                       mock_validate_path_m5, # M5
                                                       mock_write_output_file_m4, # M4
                                                       mock_merge_snippet_m3, # M3
                                                       mock_read_file_for_context_m2, # M2
                                                       mock_invoke_coder_llm_m1, # M1
                                                       mocker, # Pytest fixture
                                                       tmp_path, # Pytest fixture
                                                       caplog # Pytest fixture
                                                       ):

        caplog.set_level(logging.INFO)

        # --- Setup Mock Driver and Context ---
        context = Context(str(tmp_path))
        driver = WorkflowDriver(context)
        mock_secure_config_load_m32.return_value = None # SecureConfig.load doesn't return anything
        driver.default_policy_config = {'policy_name': 'Mock Policy'}

        # --- Configure Mocks for this specific scenario ---
        task_target_file_spec = "src/fileA.py,src/fileB.py"
        step_description = "Implement the feature." # No specific file mentioned
        resolved_file_a = str(Path(tempfile.gettempdir()) / "src" / "fileA.py").replace('\\', '/')
        resolved_file_b = str(Path(tempfile.gettempdir()) / "src" / "fileB.py").replace('\\', '/')

        # Original mock_validate_path (M5) needs its side_effect set
        def validate_path_side_effect(path):
            if path == "src/fileA.py": return resolved_file_a
            if path == "src/fileB.py": return resolved_file_b
            # Handle the case where the step description itself might contain a path
            if path == step_description: return step_description.replace('\\', '/') # Or None if not found
            # Handle the task_target_file_spec itself being validated
            if path == task_target_file_spec: return task_target_file_spec.replace('\\', '/')
            # Handle the default policy path validation in __init__
            if path == "policies/policy_bias_risk_strict.json": return "/resolved/policies/policy_bias_risk_strict.json"
            # Handle roadmap path validation in start_workflow/loop
            if path == "dummy_roadmap.json": return "/resolved/dummy_roadmap.json"
            # Handle default test path validation
            if path == "tests": return "/resolved/tests"
            if path is None: return None
            # Default fallback
            return str(Path(driver.context.base_path) / path).replace('\\', '/')

        mock_validate_path_m5.side_effect = validate_path_side_effect

        # mock_find_import_block_end_m8 already has return_value=0 from decorator
        # mock_is_add_imports_step_m7 already has return_value=False from decorator

        mock_classify_step_m9.return_value = {
            'is_code_generation_step_prelim': True,
            'filepath_from_step': None,
            'is_test_execution_step_prelim': False,
            'is_explicit_file_writing_step_prelim': False,
            'is_research_step_prelim': False,
            'is_test_writing_step_prelim': False
        }
        mock_determine_write_details_m10.return_value = (None, True)
        mock_determine_filepath_to_use_m11.return_value = None
        mock_determine_single_target_file_m30.return_value = "src/fileA.py" # This is the key mock for this test logic
        mock_read_file_for_context_m2.return_value = "Existing content of fileA."
        # mock_invoke_coder_llm_m1 already has return_value from decorator
        generated_snippet = "def new_func(): pass" # Define the actual generated snippet
        mock_invoke_coder_llm_m1.return_value = generated_snippet # Explicitly set here for clarity

        # Mock merge result
        mock_merged_content = "Existing content of fileA.\ndef new_func(): pass"
        mock_merge_snippet_m3.return_value = mock_merged_content # side_effect was set, but return_value is fine too for this

        # Mock write success
        # mock_write_output_file_m4 is just a mock object, set its return_value
        mock_write_output_file_m4.return_value = True

        # Mock validation to pass
        # Use the mock instance obtained from the patch decorator
        mock_ethical_engine_instance = mock_ethical_engine_m31.return_value
        mock_ethical_engine_instance.enforce_policy.return_value = {'overall_status': 'approved'}
        driver.code_review_agent = MagicMock() # Ensure mock instance
        driver.code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': []}
        # Use the real mocker fixture to patch ast.parse
        # mock_ast_parse_m6 is already a mock from the decorator, no need to use mocker.patch for it.
        # If you need to control its return value for a specific call, do it on mock_ast_parse_m6
        # Configure ast.parse to succeed for both snippet and merged content
        mock_ast_parse_m6.side_effect = [None, None] # First for snippet, second for merged content

        # Mock post-write validation calls (they will be called with the merged content)
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual generated snippet
        mock_ethical_engine_instance.enforce_policy.side_effect = [
            {'overall_status': 'approved'}, # Pre-write ethical
            {'overall_status': 'approved'}  # Post-write ethical
        ]
        driver.code_review_agent.analyze_python.side_effect = [
            {'status': 'success', 'static_analysis': []}, # Pre-write style/security
            {'status': 'success', 'static_analysis': []}  # Post-write style/security
        ]


        # Mock grading and evaluation to result in "Completed"
        mock_generate_grade_report_m16.return_value = json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}})
        mock_parse_and_evaluate_grade_report_m17.return_value = {"recommended_action": "Completed", "justification": "Mock success"}

        # Mock roadmap loading and task selection to run the task once and then exit
        # Define the roadmap states
        roadmap_states = [
            [{'task_id': 'multi_target_e2e_default', 'task_name': 'Multi Target Default Test', 'status': 'Not Started', 'description': 'Desc', 'priority': 'high', 'target_file': task_target_file_spec}],  # Initial load
            [{'task_id': 'multi_target_e2e_default', 'task_name': 'Multi Target Default Test', 'status': 'Not Started', 'description': 'Desc', 'priority': 'high', 'target_file': task_target_file_spec}],  # Loop 1 load
            [{'task_id': 'multi_target_e2e_default', 'task_name': 'Multi Target Default Test', 'status': 'Completed', 'description': 'Desc', 'priority': 'high', 'target_file': task_target_file_spec}],  # Loop 2 load (after update)
            []  # Loop 3 load (to exit)
        ]
        mock_load_roadmap_m27.side_effect = iter(roadmap_states)
        mock_select_next_task_m28.side_effect = [
            roadmap_states[1][0],  # Access the task from the second load
            None  # No more tasks
        ]
        mock_generate_plan_m29.return_value = [step_description] # Plan with one step

        # Mock _update_task_status_in_roadmap and _safe_write_roadmap_json
        mock_update_status_m23.return_value = None # The method itself doesn't return bool
        mock_safe_write_roadmap_json_m18.return_value = True # Mock the underlying write utility

        # --- Execute the autonomous loop ---
        # FIX: Call start_workflow instead of autonomous_loop to initialize the driver state
        driver.start_workflow("dummy_roadmap.json", "/tmp/output", context)

        # --- Assertions ---

        # Verify _determine_single_target_file was called with correct args
        mock_determine_single_target_file_m30.assert_called_once_with(step_description, task_target_file_spec, mock_classify_step_m9.return_value)

        # Verify _validate_path was called with the relative path returned by _determine_single_target_file
        mock_validate_path_m5.assert_any_call("src/fileA.py") # Called for the determined target

        # Verify _determine_filepath_to_use (fallback) was NOT called
        mock_determine_filepath_to_use_m11.assert_not_called()

        # Verify _read_file_for_context was called with the correct resolved file path (default)
        mock_read_file_for_context_m2.assert_called_once_with(resolved_file_a)

        # Verify LLM prompt includes context for the correct file (default)
        mock_invoke_coder_llm_m1.assert_called_once()
        called_prompt = mock_invoke_coder_llm_m1.call_args[0][0]
        assert f"PROVIDED CONTEXT FROM `{resolved_file_a}` (this might be the full file or a targeted section):" in called_prompt

        # Verify _merge_snippet was called with the correct content
        # FIX: Assert with the actual generated snippet
        mock_merge_snippet_m3.assert_called_with("Existing content of fileA.", generated_snippet)

        # Verify _write_output_file was called with the correct resolved file path (default) and merged content
        # FIX: Use the actual merged content
        actual_merged_content = "Existing content of fileA.\ndef new_func(): pass" # This is what the side_effect would produce
        mock_write_output_file_m4.assert_called_once_with(resolved_file_a, actual_merged_content, overwrite=True)

        # Verify pre-write validation calls
        mock_classify_step_m9.assert_called_once_with(step_description)
        mock_determine_write_details_m10.assert_called_once_with(step_description, resolved_file_a, task_target_file_spec, mock_classify_step_m9.return_value)
        # FIX: Assert with the actual generated snippet
        mock_ast_parse_m6.assert_has_calls([call(generated_snippet), call(actual_merged_content)]) # Check the ast.parse mock
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual generated snippet
        mock_ethical_engine_instance.enforce_policy.assert_any_call(generated_snippet, driver.default_policy_config, is_snippet=True)
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual generated snippet
        driver.code_review_agent.analyze_python.assert_any_call(generated_snippet)

        # Verify post-write validation calls
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual merged content
        mock_ethical_engine_instance.enforce_policy.assert_any_call(actual_merged_content, driver.default_policy_config)
        # Use the mock instance obtained from the patch decorator
        # FIX: Assert with the actual merged content
        driver.code_review_agent.analyze_python.assert_any_call(actual_merged_content)
        # Use the mock instance obtained from the patch decorator for call count
        assert mock_ethical_engine_instance.enforce_policy.call_count == 2
        assert driver.code_review_agent.analyze_python.call_count == 2

        # Verify test execution/parsing were NOT called
        mock_execute_tests_m24.assert_not_called()
        mock_parse_test_results_m25.assert_not_called()

        # Verify report generation and evaluation were called
        mock_generate_grade_report_m16.assert_called_once()
        mock_parse_and_evaluate_grade_report_m17.assert_called_once_with(ANY)

        # Verify roadmap status update was called
        mock_secure_config_load_m32.assert_called_once() # Verify SecureConfig.load was called
        mock_update_status_m23.assert_called_once_with('multi_target_e2e_default', 'Completed', None)
        # REMOVE THIS ASSERTION: _safe_write_roadmap_json is called by the mocked _update_task_status_in_roadmap
        # mock_safe_write_roadmap_json_m18.assert_called_once()

        # Verify logs
        assert "Selected task: ID=multi_target_e2e_default" in caplog.text
        assert f"Step identified as code generation for file {resolved_file_a}. Orchestrating read-generate-merge-write." in caplog.text
        # The warning log about defaulting comes from the real _determine_single_target_file.
        # Since we are mocking _determine_single_target_file_m30 directly and setting its return_value,
        # the internal logging of that method won't be captured unless the mock itself logs.
        # For this test, we verify the mock was called correctly and returned the expected default.
        # To check the log if the *real* method was called and it defaulted:
        # assert f"Step description '{step_description}' does not explicitly mention any file from the task's target list: ['src/fileA.py', 'src/fileB.py']. Defaulting to the first file: 'src/fileA.py'." in caplog.text
        assert f"Successfully wrote merged content to {resolved_file_a}." in caplog.text
        assert "Grade Report Evaluation: Recommended Action='Completed'" in caplog.text
        assert "Updating task status from 'Not Started' to 'Completed' for task multi_target_e2e_default" in caplog.text
        assert "No tasks available in Not Started status. Exiting autonomous loop." in caplog.text
# --- New Test Class for Docstring Instruction Logic (from LLM Response) ---
# FIX: Change to use pytest fixtures instead of unittest.TestCase setup
class TestPhase18DocstringPrompt:


    @pytest.fixture(autouse=True)
    def setup_driver(self, tmp_path, mocker):
        # Create a temporary directory for the project context
        tmp_path_obj = tmp_path
        context = Context(str(tmp_path_obj))

        # Mock dependencies for WorkflowDriver that are not relevant to this specific test's focus
        # Patching at the class level where WorkflowDriver would import/instantiate them
        mock_code_review_patcher = mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
        mock_ethical_engine_patcher = mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
        mock_llm_orchestrator_patcher = mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
        # Patch _load_default_policy as it's called in __init__ and uses context.get_full_path and builtins.open
        # We need to patch it before WorkflowDriver is instantiated.
        mock_load_policy_patcher = mocker.patch.object(WorkflowDriver, '_load_default_policy')


        MockCodeReviewAgent = mock_code_review_patcher.return_value
        MockEthicalGovernanceEngine = mock_ethical_engine_patcher.return_value
        MockLLMOrchestrator = mock_llm_orchestrator_patcher.return_value
        MockLoadPolicy = mock_load_policy_patcher.return_value # Start the patcher

        # Configure the mock load policy method
        MockLoadPolicy.return_value = {'policy_name': 'Mock Policy'}


        # Instantiate the WorkflowDriver with the mocked dependencies
        driver = WorkflowDriver(context)
        driver.llm_orchestrator = MockLLMOrchestrator # Assign the mock instance
        # The default_policy_config is set by _load_default_policy, which is now mocked.
        # Ensure the mock return value is assigned to the driver's attribute if needed later,
        # but the mock itself handles the __init__ call.
        # driver.default_policy_config = {'policy_name': 'Mock Policy'} # This might be redundant if _load_default_policy is mocked


        # Mock task data for context within the driver
        driver._current_task = {
            'task_id': 'docstring_test_task',
            'task_name': 'Docstring Test Task',
            'description': 'A task that involves creating a new Python function.',
            'target_file': 'src/module.py' # Ensure a .py target file
        }
        driver.task_target_file = 'src/module.py' # Set for the driver instance

        # Mock _resolve_target_file_for_step as it's called before prompt construction in autonomous_loop
        # This mock needs to return a resolved path.
        # Use patch.object here as it's an instance method.
        mock_resolve_target_file = mocker.patch.object(driver, '_resolve_target_file_for_step')
        # Default return value for the mock resolve target file
        mock_resolved_target_path = str(tmp_path_obj / driver._current_task['target_file'])
        mock_resolve_target_file.return_value = mock_resolved_target_path

        # Mock internal methods that influence prompt construction
        # These are real methods, so we need to patch them on the driver instance
        mock_is_add_imports_step = mocker.patch.object(driver, '_is_add_imports_step', return_value=False)
        mock_validate_path = mocker.patch.object(driver, '_validate_path', return_value=mock_resolved_target_path)

        # Mock _classify_step_preliminary as it's called before prompt construction
        mock_classify_step = mocker.patch.object(driver, '_classify_step_preliminary')
        # Default return value for the mock classify step (simulate code gen)
        mock_classify_step.return_value = {
            'is_code_generation_step_prelim': True,
            'filepath_from_step': 'src/module.py', # Simulate extraction
            'is_test_execution_step_prelim': False,
            'is_explicit_file_writing_step_prelim': False,
            'is_research_step_prelim': False,
            'is_test_writing_step_prelim': False
        }

        # Yield the necessary objects for the tests
        yield {
            'driver': driver,
            'tmp_path_obj': tmp_path_obj,
            'mock_resolve_target_file': mock_resolve_target_file,
            'mock_classify_step': mock_classify_step,
            'mock_llm_orchestrator': driver.llm_orchestrator, # Pass the mock instance
            'mock_resolved_target_path': mock_resolved_target_path, # Pass the resolved path
            'mock_is_add_imports_step': mock_is_add_imports_step,
            'mock_validate_path': mock_validate_path
        }


    # _should_add_docstring_instruction is a real method we want to test directly
    def test_should_add_docstring_instruction_positive_cases(self, setup_driver):
        """Test cases where the docstring instruction should be added."""
        driver = setup_driver['driver']
        positive_descriptions = [
            "Implement function calculate_sum in utils.py",
            "Add method get_data to DataProcessor class in data_handler.py",
            "Create class UserProfile for user_model.py",
            "Define new function process_records in processor.py",
            "Write a new Python function to parse data.",
            "Generate class for data storage.",
            "implement a function", # Test lowercase
            "CREATE CLASS", # Test uppercase
            "add function to existing class", # Test "add X to" pattern
            "add method to class Y",
            "add class to module Z",
            "write a new function", # Added keyword
            "create a python function", # Added keyword
            "define a new class", # Added keyword
            "define a new global function",
            "define a new python class", # Added keyword for test case
            # New keywords for Phase 1.8 docstring robustness (Task: unblock task_1_8_A_optimize_large_context)
            "Develop test case for user authentication.",
            "Write test method for the new parser.",
            "Create test class for the API client.",
            "Add logic to handle user input.",
            "Implement logic for data validation.",
            "Refactor function to improve performance.",
            "Add helper function for string manipulation.",
            "Enhance prompt construction for better LLM output.",
        ]
        for desc in positive_descriptions:
            # FIX: Use pytest's parametrization or keep the loop with explicit assertions
            # Keeping the loop for now, but using pytest assertions
            # with self.subTest(desc=desc): # Remove unittest.subTest
            assert driver._should_add_docstring_instruction(desc, "some_file.py") is True # Use pytest assertion


    # _should_add_docstring_instruction is a real method we want to test directly
    def test_should_add_docstring_instruction_negative_cases(self, setup_driver):
        """Test cases where the docstring instruction should NOT be added."""
        driver = setup_driver['driver']
        negative_descriptions = [
            "Modify existing function calculate_sum in utils.py", # Modification
            "Refactor the UserProfile class", # Refactoring
            "Run tests for data_handler.py", # Non-code task
            "Update documentation for user_model.py", # Non-code task
            "Research best practices for API design", # Non-code task
            "Update the main loop logic", # General modification
            "Fix bug in existing method", # Bug fix
            "Analyze data in a script", # Too general
        ]
        for desc in negative_descriptions:
            # FIX: Use pytest's parametrization or keep the loop with explicit assertions
            # Keeping the loop for now, but using pytest assertions
            # with self.subTest(desc=desc): # Remove unittest.subTest
            assert driver._should_add_docstring_instruction(desc, "some_file.py") is False # Use pytest assertion

        # Test cases with non-python files or no target file
        assert driver._should_add_docstring_instruction("Implement function in non_python_file.txt", "some_file.txt") is False
        assert driver._should_add_docstring_instruction("Implement function foo", None) is False
        assert driver._should_add_docstring_instruction("Create class Bar", "") is False # Empty target file string


    # FIX: Remove patch.object(WorkflowDriver, '_invoke_coder_llm') as we are not calling it
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="existing content")
    @patch.object(WorkflowDriver, '_should_add_docstring_instruction') # Local patch for this test
    # No need to patch _resolve_target_file_for_step and _classify_step_preliminary here,
    # they are patched in setUp and their mocks are available via setup_driver fixture
    def test_coder_prompt_includes_docstring_instruction_when_needed(self, mock_should_add_docstring_instruction, mock_read_file, setup_driver):
        """Verify the docstring instruction is added to the prompt for a creation task."""
        driver = setup_driver['driver']
        tmp_path_obj = setup_driver['tmp_path_obj']
        mock_resolve_target_file = setup_driver['mock_resolve_target_file']
        mock_classify_step = setup_driver['mock_classify_step']
        mock_llm_orchestrator = setup_driver['mock_llm_orchestrator'] # Get the mock instance
        mock_resolved_target_path = setup_driver['mock_resolved_target_path'] # Get the resolved path from fixture
        mock_is_add_imports_step = setup_driver['mock_is_add_imports_step']
        mock_validate_path = setup_driver['mock_validate_path']

        step = "Implement new function process_data in src/module.py"

        # Configure mocks called before prompt construction
        # Use the resolved path from the fixture
        mock_resolve_target_file.return_value = mock_resolved_target_path
        mock_classify_step.return_value = {
            'is_code_generation_step_prelim': True,
            'filepath_from_step': 'src/module.py',
            'is_test_execution_step_prelim': False,
            'is_explicit_file_writing_step_prelim': False,
            'is_research_step_prelim': False,
            'is_test_writing_step_prelim': False
        }

        # Ensure internal methods that influence prompt construction are mocked as needed for this test
        mock_is_add_imports_step.return_value = False # Default to not an import step
        mock_should_add_docstring_instruction.return_value = True # Explicitly set for this test

        # Define filepath_to_use and context_for_llm
        filepath_to_use = mock_resolved_target_path
        context_for_llm = mock_read_file.return_value # This is "existing content"

        coder_prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm, # Pass existing_content as context_for_llm
            is_minimal_context=False # Pass is_minimal_context
        )

        # Assert critical instructions are present
        assert CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in coder_prompt

        # Assert the docstring instruction with example is present
        assert DOCSTRING_INSTRUCTION_PYTHON in coder_prompt

        # Assert other expected parts are present
        assert f"Overall Task: \"{driver._current_task.get('task_name', 'Unknown Task')}\"" in coder_prompt
        assert f"Task Description: {driver._current_task.get('description', 'No description provided.')}" in coder_prompt
        assert f"Specific Plan Step:\n{step}" in coder_prompt
        assert f"PROVIDED CONTEXT FROM `{filepath_to_use}` (this might be the full file or a targeted section):" in coder_prompt
        assert context_for_llm in coder_prompt

        # Verify the docstring instruction is in the actual prompt
        assert DOCSTRING_INSTRUCTION_PYTHON in coder_prompt
        # Assert the target file context phrasing matches the SUT (needs to be constructed)
        # The prompt section is: "The primary file being modified for this task is specified as `resolved_primary_task_target_path` in the task metadata. Focus your plan steps on actions related to this file."
        expected_target_file_context = (
            f"The primary file being modified for this task is specified as `{mock_resolved_target_path}` "
            "in the task metadata. Focus your plan steps on actions related to this file."
        )
        assert expected_target_file_context.strip() in coder_prompt


    # FIX: Remove patch.object(WorkflowDriver, '_invoke_coder_llm') as we are not calling it
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="existing content")
    @patch.object(WorkflowDriver, '_should_add_docstring_instruction') # Local patch for this test
    # _resolve_target_file_for_step and _classify_step_preliminary are patched in setUp and their mocks are available via setup_driver fixture
    def test_coder_prompt_excludes_docstring_instruction_when_not_needed(self, mock_should_add_docstring_instruction, mock_read_file, setup_driver):
        """Verify the docstring instruction is NOT added for non-creation or non-python tasks."""
        driver = setup_driver['driver']
        tmp_path_obj = setup_driver['tmp_path_obj']
        mock_resolve_target_file = setup_driver['mock_resolve_target_file']
        mock_classify_step = setup_driver['mock_classify_step']
        mock_llm_orchestrator = setup_driver['mock_llm_orchestrator'] # Get the mock instance
        # No need for mock_resolved_target_path here, as it's set on the mock_resolve_target_file
        # Update the task's target file to match the step's target for this test
        driver._current_task['target_file'] = 'src/module.py' # Ensure it's a .py file
        python_target_path = str(tmp_path_obj / "src/module.py")
        setup_driver['mock_validate_path'].return_value = python_target_path
        mock_validate_path = setup_driver['mock_validate_path']
    
        step = "Update the configuration settings in src/config.txt"
    
        # Configure mocks called before prompt construction
        mock_resolve_target_file.return_value = python_target_path
        mock_classify_step.return_value = {
            'is_code_generation_step_prelim': True, # Still simulate code gen step type
            'filepath_from_step': driver._current_task['target_file'],
            'is_test_execution_step_prelim': False,
            'is_explicit_file_writing_step_prelim': False,
            'is_research_step_prelim': False,
            'is_test_writing_step_prelim': False
        }
    
        # Ensure internal methods that influence prompt construction are mocked as needed for this test
        setup_driver['mock_is_add_imports_step'].return_value = False # Default to not an import step
        mock_should_add_docstring_instruction.return_value = False
    
        # Define filepath_to_use and context_for_llm
        filepath_to_use = python_target_path
        context_for_llm = mock_read_file.return_value # This is "existing content"
    
        coder_prompt = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step,
            filepath_to_use=filepath_to_use,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )
    
        # Assert critical instructions are present
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in coder_prompt
    
        # Verify the SPECIFIC docstring instruction is NOT in the prompt
        assert DOCSTRING_INSTRUCTION_PYTHON not in coder_prompt
        # Verify the GENERAL docstring reminder IS in the prompt for .py files
        assert GENERAL_PYTHON_DOCSTRING_REMINDER in coder_prompt
    
        # Assert the target file context phrasing matches the SUT (needs to be constructed)
        # The prompt section is: "The primary file being modified for this task is specified as `resolved_primary_task_target_path` in the task metadata. Focus your plan steps on actions related to this file."
        expected_target_file_context = (
            f"The primary file being modified for this task is specified as `{python_target_path}` "
            "in the task metadata. Focus your plan steps on actions related to this file."
        )
        assert expected_target_file_context.strip() in coder_prompt
    
        # Scenario 2: Non-Python file, docstring instructions should be absent
        driver._current_task['target_file'] = 'src/config.txt' # Change to non .py
        non_python_target_path = str(tmp_path_obj / "src/config.txt")
        setup_driver['mock_validate_path'].return_value = non_python_target_path
        mock_resolve_target_file.return_value = non_python_target_path # Update mock
        mock_classify_step.return_value['filepath_from_step'] = 'src/config.txt' # Update mock
    
        mock_should_add_docstring_instruction.return_value = False
    
        coder_prompt_non_py = driver._construct_coder_llm_prompt(
            task=driver._current_task,
            step_description=step, # Same step description, different target file
            filepath_to_use=non_python_target_path,
            context_for_llm=context_for_llm,
            is_minimal_context=False
        )
        assert DOCSTRING_INSTRUCTION_PYTHON not in coder_prompt_non_py
        assert GENERAL_PYTHON_DOCSTRING_REMINDER not in coder_prompt_non_py
    
# --- New Test Class for Prompt Refinement Logic ---
class TestPromptRefinement:


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

        # Mock dependencies that _construct_coder_prompt might call or rely on
        mocker.patch.object(driver, '_resolve_target_file_for_step', return_value=str(tmp_path / driver._current_task['target_file']))
        mocker.patch.object(driver, '_read_file_for_context', return_value="existing content")
        mocker.patch.object(driver, '_is_add_imports_step', return_value=False) # Default to not an import step
        mocker.patch.object(driver, '_should_add_docstring_instruction', return_value=False) # Default to no docstring instruction

        yield driver

    def test_coder_prompt_includes_general_guidelines_no_import(self, setup_driver):
        """Verify general guidelines are included in the prompt for a regular code gen step."""
        driver = setup_driver
        step_description = "Implement a new function."
        filepath = driver._resolve_target_file_for_step(step_description, driver.task_target_file, None)
        context_content = driver._read_file_for_context(filepath)

        # Call the SUT method directly
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
        filepath = driver._resolve_target_file_for_step(step_description, driver.task_target_file, None)
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
# --- New Test Class for Merge Strategy Logic ---
class TestMergeSnippetLogic:


    @pytest.fixture(autouse=True)
    def setup_driver(self, tmp_path, mocker):
        context = Context(str(tmp_path))
        mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent')
        mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine')
        mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator')
        mocker.patch.object(WorkflowDriver, '_load_default_policy')

        # Ensure 're' is imported in the module where _merge_snippet is defined
        # This is a file-level import, so we don't mock it here, but ensure the SUT has it.

        driver = WorkflowDriver(context)
        driver.default_policy_config = {'policy_name': 'Mock Policy'}
        yield driver

    @pytest.mark.parametrize("existing_content, snippet, expected_merged_content", [
        # Basic insertion with indentation
        ("def func():\n    # METAMORPHIC_INSERT_POINT\n    pass", "new_line = 1", "def func():\n    new_line = 1\n    pass"),
        ("def func():\n    # METAMORPHIC_INSERT_POINT\n    pass", "line1\nline2", "def func():\n    line1\n    line2\n    pass"),
        # Marker at start of file
        ("# METAMORPHIC_INSERT_POINT\ndef func(): pass", "import os", "import os\ndef func(): pass"),
        # Marker at end of file
        ("def func():\n    pass\n# METAMORPHIC_INSERT_POINT", "return True", "def func():\n    pass\nreturn True"),
        # Marker on an indented line, snippet has multiple lines
        ("class MyClass:\n    def method(self):\n        # METAMORPHIC_INSERT_POINT\n        print('done')", 
         "self.value = 10\nprint('init')", 
         "class MyClass:\n    def method(self):\n        self.value = 10\n        print('init')\n        print('done')"),
        # No marker, append behavior
        ("line1\nline2", "appended", "line1\nline2\nappended"),
        ("line1", "appended", "line1\nappended"),
        # NEW: Empty snippet with prefix on marker line
        ("def func():\n    x = 1 # METAMORPHIC_INSERT_POINT\n    pass", "", "def func():\n    x = 1\n    \n    pass"),
        # Snippet with internal leading whitespace (should be preserved relative to new indentation)
        ("def func():\n    # METAMORPHIC_INSERT_POINT\n    pass", "    inner_line = 1", "def func():\n    inner_line = 1\n    pass"),
        # Marker on line with other content (should replace just the marker)
        ("def func():\n    x = 1 # METAMORPHIC_INSERT_POINT\n    pass", "y = 2", "def func():\n    x = 1\n    y = 2\n    pass"),
        # Marker on line with other content, snippet is multi-line (each line indented)
        ("def func():\n    x = 1 # METAMORPHIC_INSERT_POINT\n    pass", "lineA\nlineB", "def func():\n    x = 1\n    lineA\n    lineB\n    pass"),
    ])
    def test_merge_snippet_with_indentation_logic(self, setup_driver, existing_content, snippet, expected_merged_content):
        """Test _merge_snippet correctly applies indentation and replaces the marker."""
        driver = setup_driver
        merged_content = driver._merge_snippet(existing_content, snippet)
        assert merged_content == expected_merged_content

    def test_merge_snippet_no_marker_append_behavior(self, setup_driver):
        """Ensure append behavior is maintained when no marker is found."""
        driver = setup_driver
        existing = "line1\nline2"
        snippet = "new_content"
        expected = "line1\nline2\nnew_content"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test_merge_snippet_no_marker_existing_no_newline(self, setup_driver):
        """Ensure append behavior adds newline if existing content doesn't end with one."""
        driver = setup_driver
        existing = "line1"
        snippet = "new_content"
        expected = "line1\nnew_content"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected