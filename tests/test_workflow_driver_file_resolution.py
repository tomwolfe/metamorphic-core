# tests/test_workflow_driver_file_resolution.py
import pytest
from unittest.mock import patch, MagicMock
from src.core.automation.workflow_driver import WorkflowDriver, Context

@pytest.fixture
def driver_for_file_resolution(tmp_path, mocker):
    """Fixture to create a WorkflowDriver instance for testing file resolution."""
    mock_context = Context(str(tmp_path)) # Create a real Context for path resolution
    mocker.patch('src.core.automation.workflow_driver.CodeReviewAgent') # Mock dependencies
    mocker.patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') # Mock dependencies
    mocker.patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') # Mock dependencies
    mocker.patch.object(WorkflowDriver, '_load_default_policy') # Mock internal method
    mocker.patch('src.core.automation.workflow_driver.logger') # Patch the module-level logger
    driver = WorkflowDriver(mock_context) # Instantiate the driver
    return driver

class TestFileResolution:
    def test_resolve_target_file_chooses_test_file_for_test_step(self, driver_for_file_resolution):
        """
        Tests that for a multi-target task, a test-writing step correctly
        resolves to the test file from the target list.
        """
        driver = driver_for_file_resolution
        task_target_spec = "src/core/automation/workflow_driver.py, tests/test_phase1_8_features.py"
        step_description = "Update the unit tests to cover the new logic."
        prelim_flags = {'is_code_generation_step_prelim': True, 'is_test_writing_step_prelim': True}

        resolved_path = driver._resolve_target_file_for_step(step_description, task_target_spec, prelim_flags)
        
        expected_path = driver.context.get_full_path("tests/test_phase1_8_features.py")
        assert resolved_path == expected_path
        driver.logger.info.assert_any_call("Test writing step: Using test file 'tests/test_phase1_8_features.py' from task's target list.")

    def test_resolve_target_file_falls_back_to_derivation(self, driver_for_file_resolution):
        """
        Tests that if no test file is in the multi-target list, it falls back to
        deriving the test file path from the primary source file.
        """
        driver = driver_for_file_resolution
        task_target_spec = "src/core/automation/workflow_driver.py, src/core/llm_orchestration.py"
        step_description = "Write unit tests for the new feature."
        prelim_flags = {'is_code_generation_step_prelim': True, 'is_test_writing_step_prelim': True}

        resolved_path = driver._resolve_target_file_for_step(step_description, task_target_spec, prelim_flags)
        
        expected_path = driver.context.get_full_path("tests/workflow_driver_test.py")
        assert resolved_path == expected_path
        driver.logger.info.assert_any_call("Test writing step: Derived test file path 'tests/workflow_driver_test.py' from task target 'src/core/automation/workflow_driver.py'.")