# File: tests/test_workflow_driver.py
import pytest
import html
import shutil
import subprocess

# Assuming workflow_driver.py is in src.core.automation
from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT
import os
import logging

# Assuming write_file is in src.cli
from src.cli.write_file import write_file, file_exists
from pathlib import Path
import json
from unittest.mock import MagicMock, patch, ANY, call
import re

# Removed direct import of agents as they are mocked via fixture/patch
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from datetime import datetime # Import datetime for the fix
import uuid
import builtins # Import builtins for mocking open

# Set up logging for tests
# Check if handlers exist to avoid adding duplicate handlers in subsequent test runs
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Use the correct logger name for the module
# FIX: Correct logger name
logger = logging.getLogger(__name__) # Use __name__ for the logger name

# Define a maximum file size for reading (e.g., 1MB)
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion, matching the value in workflow_driver.py
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"

@pytest.fixture
def test_driver(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation within the fixture setup
    # Use the full path for patching if necessary, e.g., 'src.core.automation.workflow_driver.CodeReviewAgent'
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:
        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        # Mock the policy loading within the engine mock
        # Note: The actual WorkflowDriver loads policy via _load_default_policy which uses builtins.open
        # This mock might not be strictly necessary if builtins.open is patched globally, but keep for clarity.
        # mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}


        driver = WorkflowDriver(context)
        # Ensure LLM orchestrator mock is set up
        driver.llm_orchestrator = MagicMock()
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        # Assign mocked instances (this happens automatically if patching instantiation, but explicit is fine)
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        # Set the default policy config directly after mocking load_policy_from_json
        # This is needed because the real _load_default_policy might be called if builtins.open isn't patched globally
        driver.default_policy_config = {'policy_name': 'Mock Policy'}


        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance
        }

# FIX: Modify test_driver_validation fixture to patch Context.get_full_path
@pytest.fixture
def test_driver_validation(tmp_path, mocker): # Add mocker here
    # Patch Context.get_full_path FIRST
    mock_get_full_path = mocker.patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")

    context = Context(str(tmp_path)) # Real Context created, but its get_full_path is now mocked

    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:
        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        # Mock the policy loading within the engine mock
        mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        # Instantiate WorkflowDriver using the created context object
        # __init__ is called here, which calls _load_default_policy, which calls context.get_full_path
        # Since context.get_full_path is now mocked, it will return "/resolved/policies/policy_bias_risk_strict.json"
        driver = WorkflowDriver(context)
        # Ensure LLM orchestrator mock is set up
        driver.llm_orchestrator = MagicMock()
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        # Assign mocked instances
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        # Set the default policy config directly after mocking load_policy_from_json
        driver.default_policy_config = {'policy_name': 'Mock Policy'}

        # Add attributes needed for tests that might not be set by __init__ or autonomous_loop setup
        driver._current_task_results = {}
        driver.remediation_attempts = 0 # Initialize remediation counter for tests
        driver.remediation_occurred_in_pass = False # Initialize flag

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance,
            'mock_get_full_path': mock_get_full_path # Yield the mock so tests can assert on it
        }


def create_mock_roadmap_file(content, tmp_path, is_json=True):
    """Creates a mock roadmap file in the temporary directory."""
    if is_json:
        file_path = tmp_path / "ROADMAP.json"
    else:
        file_path = tmp_path / "ROADMAP.txt"
    with open(file_path, "w") as f:
        f.write(content)
    return str(file_path)

# Helper task lists for tests
task_list_not_started = [{'task_id': 'mock_task', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}]
task_list_completed = [{'task_id': 'mock_task', 'task_name': 'Mock Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High'}]
task_list_blocked = [{'task_id': 'mock_task', 'task_name': 'Mock Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High'}]

# Corrected expected data for safe_write_roadmap_json assertion
# This list should match the structure and content of the task after it's marked completed
task_list_completed_expected_write = [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Completed', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}]

# Corrected expected data for success flow
task_list_success_completed_expected_write = [{'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}]

# Corrected expected data for ethical reject flow
task_list_ethical_blocked_expected_write = [{'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py'}]

# Corrected expected data for security high flow
task_list_security_blocked_expected_write = [{'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py'}]

# Corrected expected data for multiple code steps flow
task_list_multiple_code_completed_expected_write = [{'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}]

# Corrected expected data for conceptual step flow
task_list_conceptual_completed_expected_write = [{'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Completed', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'}]

# FIX: Define the correct expected data for the prioritize target file test
task_list_prioritize_target_completed_expected_write = [{'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Completed', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}]

# ADDED: Expected data for validation error -> blocked flow
task_list_validation_error_blocked_expected_write = [{'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py'}]

# ADDED: Expected data for generic write error -> blocked flow
task_list_generic_error_blocked_expected_write = [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Blocked', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}]


class TestWorkflowDriver:


    # --- Tests for start_workflow method ---
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_start_workflow_sets_attributes_and_calls_loop(self, mock_get_full_path, mock_load_roadmap, test_driver, tmp_path, mocker):
        """Test that start_workflow correctly sets attributes and calls autonomous_loop."""
        # Mock logging to avoid clutter in this specific test, focusing on calls
        mocker.patch('logging.Logger.info')
        mocker.patch('logging.Logger.error')
        mocker.patch('logging.Logger.warning')

        driver = test_driver['driver']
        mock_autonomous_loop = mocker.patch.object(driver, 'autonomous_loop')
        mock_context = Context(str(tmp_path))

        driver.start_workflow("path/to/roadmap.json", str(tmp_path / "output"), mock_context)

        assert driver.roadmap_path == "path/to/roadmap.json"
        assert driver.output_dir == str(tmp_path / "output")
        assert driver.context is mock_context

        # load_roadmap is called once in start_workflow before the loop
        mock_get_full_path.assert_called_once_with("path/to/roadmap.json")
        mock_load_roadmap.assert_called_once_with("/resolved/path/to/roadmap.json")
        mock_autonomous_loop.assert_called_once()

    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_start_workflow_with_empty_strings(self, mock_get_full_path, mock_load_roadmap, test_driver, tmp_path, mocker):
        """Test start_workflow handles empty string inputs."""
        # Mock logging to avoid clutter in this specific test, focusing on calls
        mocker.patch('logging.Logger.info')
        mocker.patch('logging.Logger.error')
        mocker.patch('logging.Logger.warning')

        driver = test_driver['driver']
        mock_autonomous_loop = mocker.patch.object(driver, 'autonomous_loop')
        mock_context = Context(str(tmp_path))

        driver.start_workflow("", "", mock_context)

        assert driver.roadmap_path == ""
        assert driver.output_dir == ""
        assert driver.context == mock_context
        mock_get_full_path.assert_called_once_with("")
        mock_load_roadmap.assert_called_once_with("/resolved/")
        mock_autonomous_loop.assert_called_once()

    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[]) # Mock load_roadmap itself
    @patch.object(Context, 'get_full_path', return_value=None) # Mock get_full_path to return None
    def test_start_workflow_with_none(self, mock_get_full_path, mock_load_roadmap, test_driver, tmp_path, mocker, caplog):
        """Test start_workflow handles None roadmap_path gracefully by failing path resolution."""
        caplog.set_level(logging.ERROR)
        driver = test_driver['driver']

        mock_autonomous_loop = mocker.patch.object(driver, 'autonomous_loop')
        mock_context_passed_in = Context(str(tmp_path))

        driver.start_workflow(None, None, mock_context_passed_in) # Pass None for roadmap_path

        assert driver.roadmap_path is None
        assert driver.output_dir is None

        # Assert get_full_path was called with None
        mock_get_full_path.assert_called_once_with(None)
        # Assert load_roadmap was NOT called because get_full_path returned None
        mock_load_roadmap.assert_not_called()
        # Assert tasks list remains empty
        assert driver.tasks == []

        assert driver.context == mock_context_passed_in

        # Assert autonomous_loop was NOT called because start_workflow exited early
        mock_autonomous_loop.assert_not_called()
        # Assert the specific error message was logged
        assert "Invalid roadmap path provided: None" in caplog.text


    # --- Tests for autonomous_loop orchestration ---
    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call count and arguments
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[[], [], []]) # Initial load, Loop 1 load, Loop 2 load (empty)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_autonomous_loop_basic_logging(self, mock_get_full_path, mock_load_roadmap, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop logs the start and end messages when no tasks are available."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        driver.roadmap_path = "dummy_roadmap.json"

        # Mock select_next_task to always return None
        mocker.patch.object(driver, 'select_next_task', return_value=None)

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        assert 'Starting autonomous loop iteration' in caplog.text
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text # This assertion should now pass with the fix in workflow_driver.py
        # load_roadmap is called once in start_workflow, then once per loop iteration (only 1 iteration runs here)
        assert mock_load_roadmap.call_count == 2 # start_workflow + first loop iteration
        mock_load_roadmap.assert_any_call(f"/resolved/{driver.roadmap_path}")
        # get_full_path is called once in start_workflow, then once per loop iteration
        assert mock_get_full_path.call_count == 2
        mock_get_full_path.assert_any_call(driver.roadmap_path)


    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Keep assertion for 'No tasks available...' log message
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'},
        None
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=[])
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}], # Initial load in start_workflow
        [{'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}], # Load at start of loop 1
        []  # Load at start of loop 2
    ])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    def test_autonomous_loop_task_selected_logging(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_get_full_path, mock_load_roadmap, mock_generate_plan, mock_select_next_task, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop logs the selected task ID when a task is found and then exits."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        driver.roadmap_path = "dummy_roadmap.json"
        task_list_1 = [{'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}]
        task_list_2 = []

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        # Assertions
        assert mock_load_roadmap.call_count == 3 # start_workflow + loop 1 + loop 2
        mock_load_roadmap.assert_any_call(f"/resolved/{driver.roadmap_path}")

        assert mock_select_next_task.call_count == 2 # Called in loop 1 and loop 2
        # Check arguments passed to select_next_task
        mock_select_next_task.assert_has_calls([
            call(task_list_1), # Argument from load_roadmap in loop 1
            call(task_list_2)  # Argument from load_roadmap in loop 2
        ])

        assert mock_get_full_path.call_count == 3 # start_workflow + loop 1 + loop 2
        mock_get_full_path.assert_any_call(driver.roadmap_path)

        assert 'Starting autonomous loop iteration' in caplog.text # Logged twice
        assert caplog.text.count('Starting autonomous loop iteration') == 2
        assert 'Selected task: ID=mock_task_1' in caplog.text
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text # This assertion should now pass with the fix in workflow_driver.py
        # Status update should not happen as evaluation is Manual Review
        mock_safe_write_roadmap.assert_not_called()


    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Keep assertion for 'No tasks available...' log message
    @patch.object(WorkflowDriver, 'select_next_task', return_value=None)
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        # FIX: Correct the structure from [[]] to [] - The provided code already has the correct structure
        [{'task_id': 'mock_task_completed', 'task_name': 'Completed Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High'}], # Initial
        [{'task_id': 'mock_task_completed', 'task_name': 'Completed Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High'}], # Loop 1 load
        [] # Loop 2 load (just in case, though loop should exit after 1)
    ])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_autonomous_loop_no_task_logging(self, mock_get_full_path, mock_load_roadmap, mock_select_next_task, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop logs the 'No tasks available' message when no task is found."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        driver.roadmap_path = "dummy_roadmap.json"
        completed_task_list = [{'task_id': 'mock_task_completed', 'task_name': 'Completed Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High'}]

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        # load_roadmap called in start_workflow, then loop 1
        assert mock_load_roadmap.call_count == 2
        mock_load_roadmap.assert_any_call(f"/resolved/{driver.roadmap_path}")
        # select_next_task called once in loop 1
        mock_select_next_task.assert_called_once_with(completed_task_list) # Called with result of loop 1 load
        # get_full_path called in start_workflow, then loop 1
        assert mock_get_full_path.call_count == 2
        mock_get_full_path.assert_any_call(driver.roadmap_path)

        assert 'Starting autonomous loop iteration' in caplog.text # Logged once
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text # This assertion should now pass with the fix in workflow_driver.py


    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Update assertion for "EXISTING CONTENT OF" block to include trailing newline
    # FIX: Correct argument order in signature
    # FIX: Correct the typo in the patch target from _invoke_coder_llM to _invoke_coder_llm
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement feature and add logic to src/feature.py"])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'mock_task_code_write', 'task_name': 'Task Code Write', 'status': 'Not Started', 'description': 'Desc Code Write', 'priority': 'High', 'target_file': 'src/feature.py'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'mock_task_code_write', 'task_name': 'Task Code Write', 'status': 'Not Started', 'description': 'Desc Code Write', 'priority': 'High', 'target_file': 'src/feature.py'}], # Initial
        [{'task_id': 'mock_task_code_write', 'task_name': 'Task Code Write', 'status': 'Not Started', 'description': 'Desc Code Write', 'priority': 'High', 'target_file': 'src/feature.py'}], # Loop 1
        [] # Loop 2
    ])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    # Add patch for builtins.open
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_calls_write_file_with_generated_content(self,
                                                                    mock_open, # Corresponds to @patch('builtins.open', ...)
                                                                    mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                                    mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                                    mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                                    mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                                    mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                                    mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                                    mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                                    mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                                    mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                                    mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                                    mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                                    test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop calls _write_output_file with generated content when step is code gen + file write."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        mock_code_review_agent = test_driver['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver['mock_ethical_governance_engine']

        # Set return values on the mock instances from the fixture
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        driver.roadmap_path = "dummy_roadmap.json"

        # FIX: Configure mock_open for json.load
        task_list_not_started_local = [{'task_id': 'mock_task_code_write', 'task_name': 'Task Code Write', 'status': 'Not Started', 'description': 'Desc Code Write', 'priority': 'High', 'target_file': 'src/feature.py'}]
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started_local})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_called_once_with("src/feature.py")
        mock_invoke_coder_llm.assert_called_once()
        called_prompt = mock_invoke_coder_llm.call_args[0][0]
        assert "You are a Coder LLM expert in Python." in called_prompt
        assert "Overall Task: \"Task Code Write\"" in called_prompt
        assert "Specific Plan Step:\nStep 1: Implement feature and add logic to src/feature.py" in called_prompt
        assert "The primary file being modified is `src/feature.py`." in called_prompt # Added assertion for new prompt part
        # FIX: Add the trailing newline to the assertion string
        assert "EXISTING CONTENT OF `src/feature.py`:\n```python\n\n```\n" in called_prompt

        mock_merge_snippet.assert_called_once_with(mock_read_file_for_context.return_value, mock_invoke_coder_llm.return_value)
        mock_write_output_file.assert_called_once_with("src/feature.py", mock_merge_snippet.return_value, overwrite=True)

        # Assert on the mock instances from the fixture
        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_governance_engine.enforce_policy.call_count == 2
        calls = mock_ethical_governance_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write

        assert "Step identified as code generation for file src/feature.py. Orchestrating read-generate-merge-write." in caplog.text
        assert "Successfully wrote merged content to src/feature.py." in caplog.text
        assert "Running code review and security scan for src/feature.py..." in caplog.text
        assert "Running ethical analysis for src/feature.py..." in caplog.text
        # Status update should not happen
        mock_safe_write_roadmap.assert_not_called()
        assert 'Autonomous loop terminated.' in caplog.text # Added assertion


    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Update assertion for "EXISTING CONTENT OF" block to include trailing newline
    # FIX: Correct argument order in signature
    # FIX: Correct the typo in the patch target from _invoke_coder_llM to _invoke_coder_llm
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement feature and add logic to src/feature.py"])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'mock_task_code_write_exists', 'task_name': 'Task Code Write Exists', 'status': 'Not Started', 'description': 'Desc Code Write Exists', 'priority': 'High', 'target_file': 'src/feature.py'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'mock_task_code_write_exists', 'task_name': 'Task Code Write Exists', 'status': 'Not Started', 'description': 'Desc Code Write Exists', 'priority': 'High', 'target_file': 'src/feature.py'}], # Initial
        [{'task_id': 'mock_task_code_write_exists', 'task_name': 'Task Code Write Exists', 'status': 'Not Started', 'description': 'Desc Code Write Exists', 'priority': 'High', 'target_file': 'src/feature.py'}], # Loop 1
        [] # Loop 2
    ])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing file content")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    # Add patch for builtins.open
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_reads_existing_file_content(self,
                                                    mock_open, # Corresponds to @patch('builtins.open', ...)
                                                    mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                    mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                    mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                    mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                    mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                    mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                    mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                    mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                    mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                    mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                    mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                    test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop reads existing file content and includes it in the LLM prompt."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        mock_code_review_agent = test_driver['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver['mock_ethical_governance_engine']

        # Set return values on the mock instances from the fixture
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        driver.roadmap_path = "dummy_roadmap.json" # Set before start_workflow

        # FIX: Configure mock_open for json.load
        task_list_not_started_local = [{'task_id': 'mock_task_code_write_exists', 'task_name': 'Task Code Write Exists', 'status': 'Not Started', 'description': 'Desc Code Write Exists', 'priority': 'High', 'target_file': 'src/feature.py'}]
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started_local})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_called_once_with("src/feature.py")

        mock_invoke_coder_llm.assert_called_once()
        called_prompt = mock_invoke_coder_llm.call_args[0][0]

        assert "You are a Coder LLM expert in Python." in called_prompt
        assert "Overall Task: \"Task Code Write Exists\"" in called_prompt
        assert "Specific Plan Step:\nStep 1: Implement feature and add logic to src/feature.py" in called_prompt
        assert "The primary file being modified is `src/feature.py`." in called_prompt # Added assertion for new prompt part
        # FIX: Add the trailing newline to the assertion string
        assert "EXISTING CONTENT OF `src/feature.py`:\n```python\nExisting file content\n```\n" in called_prompt

        mock_merge_snippet.assert_called_once_with(mock_read_file_for_context.return_value, mock_invoke_coder_llm.return_value)
        mock_write_output_file.assert_called_once_with("src/feature.py", mock_merge_snippet.return_value, overwrite=True)

        # Assert on the mock instances from the fixture
        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_governance_engine.enforce_policy.call_count == 2
        calls = mock_ethical_governance_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write

        assert "Step identified as code generation for file src/feature.py. Orchestrating read-generate-merge-write." in caplog.text
        assert "Successfully wrote merged content to src/feature.py." in caplog.text
        assert "Running code review and security scan for src/feature.py..." in caplog.text
        assert "Running ethical analysis for src/feature.py..." in caplog.text
        # Status update should not happen
        mock_safe_write_roadmap.assert_not_called()
        assert 'Autonomous loop terminated.' in caplog.text # Added assertion


    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Update assertion for "EXISTING CONTENT OF" block to include trailing newline
    # FIX: Correct argument order in signature
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement logic in incorrect/file_from_step.py"]) # Step mentions a different file
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Not Started', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}, # Task has a target_file
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Not Started', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}], # Initial
        [{'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Not Started', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}], # Loop 1
        [{'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Completed', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing content.")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Patch _write_output_file and make it return True
    @patch.object(WorkflowDriver, 'execute_tests') # Ensure this is NOT called
    @patch.object(WorkflowDriver, '_parse_test_results') # Ensure this is NOT called
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}})) # Mock report generation
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed", "justification": "Mock evaluation"}) # Mock report evaluation
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True) # Mock roadmap write
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_prioritizes_target_file(self,
                                                    mock_open,                     # Corresponds to @patch('builtins.open', ...)
                                                    mock_safe_write_roadmap,       # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                    mock_parse_and_evaluate,       # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                    mock_generate_report,          # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                    mock_parse_test_results,       # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results')
                                                    mock_execute_tests,            # Corresponds to @patch.object(WorkflowDriver, 'execute_tests')
                                                    mock_write_output_file,        # Corresponds to @patch.object(WorkflowDriver, '_write_output_file')
                                                    mock_get_full_path,            # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                    mock_merge_snippet,            # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                    mock_read_file_for_context,    # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                    mock_load_roadmap,             # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                    mock_select_next_task,         # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                    mock_generate_plan,            # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                    mock_invoke_coder_llm,         # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                                                    test_driver_validation, caplog, tmp_path, mocker):
        """
        Test that autonomous_loop prioritizes the 'target_file' from the task
        over a filename mentioned in the plan step description.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set return values on the mock instances from the fixture
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        # FIX: Define task_list_not_started and task_list_completed for assertions
        task_list_not_started = [{'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Not Started', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}]
        task_list_completed = [{'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Completed', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()

        # Verify that the driver attempted to read the file specified in target_file, NOT the one in the step
        mock_read_file_for_context.assert_called_once_with("correct/file_from_task.py")

        # Verify LLM prompt includes the correct target file context
        mock_invoke_coder_llm.assert_called_once()
        called_prompt = mock_invoke_coder_llm.call_args[0][0]
        # This assertion should now pass with the corrected generate_solution_plan
        # FIX: Correct assertion string to match the code's prompt template
        assert "The primary file being modified is `correct/file_from_task.py`." in called_prompt
        # Should NOT use the old heuristic based on name/description
        assert "The primary file being modified for this task is" not in called_prompt
        # Ensure Task Name and Description are still present
        # FIX: Correct assertion string to match the code's prompt template
        assert 'Overall Task: "Prioritize Target File"' in called_prompt
        # --- FIX 1 APPLIED HERE ---
        assert "Task Description: Test target file prioritization." in called_prompt
        # FIX: Add the trailing newline to the assertion string
        assert "EXISTING CONTENT OF `correct/file_from_task.py`:\n```python\nExisting content.\n```\n" in called_prompt

        # Verify merge and write were called with the correct target file
        mock_merge_snippet.assert_called_once_with(mock_read_file_for_context.return_value, mock_invoke_coder_llm.return_value)
        mock_write_output_file.assert_called_once_with("correct/file_from_task.py", mock_merge_snippet.return_value, overwrite=True)

        # Verify validation steps were called with the content written to the correct file
        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_governance_engine.enforce_policy.call_count == 2
        calls = mock_ethical_governance_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write
        mock_execute_tests.assert_not_called() # No test step in this plan
        mock_parse_test_results.assert_not_called()

        # Verify report generation and evaluation
        mock_generate_report.assert_called_once()
        called_report_results = mock_generate_report.call_args[0][1]
        # Ensure validation results are included in the report data
        assert 'code_review_results' in called_report_results
        assert 'ethical_analysis_results' in called_report_results
        # --- FIX 1 APPLIED HERE: Removed incorrect assertion ---
        # assert 'test_results' in called_report_results # Should be empty/default if tests weren't run

        mock_parse_and_evaluate.assert_called_once_with(mock_generate_report.return_value)

        # Assert that open was called to read the roadmap before writing
        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')

        # safe_write_roadmap is called because the status changes to "Completed"
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, ANY)
        # Check the content passed to safe_write_roadmap
        written_data = mock_safe_write_roadmap.call_args[0][1]
        # FIX: Use the corrected expected data
        assert written_data == {'tasks': task_list_prioritize_target_completed_expected_write}


        # Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_completed)


        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_prioritize_target' in caplog.text
        assert 'Executing step 1/1: Step 1: Implement logic in incorrect/file_from_step.py' in caplog.text
        # Check the log for the file identified for code generation/write (should be the target_file)
        assert "Step identified as code generation for file correct/file_from_task.py. Orchestrating read-generate-merge-write." in caplog.text
        assert 'Successfully wrote merged content to correct/file_from_task.py.' in caplog.text
        assert 'Running code review and security scan for correct/file_from_task.py...' in caplog.text
        assert 'Running ethical analysis for correct/file_from_task.py...' in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Completed\'' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Completed\' for task task_prioritize_target' in caplog.text
        assert 'Successfully wrote updated status for task task_prioritize_target in dummy_roadmap.json' in caplog.text # Added assertion back
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text


    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Add mock for builtins.open for status update read
    # FIX: Correct argument order in signature
    # FIX: Update the assertion for _write_output_file to expect overwrite=True
    # FIX: Update the assertion for _safe_write_roadmap_json to expect the call and the 'Blocked' status
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value=None)
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Write output to error.txt", "Step 2: Another step."])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}], # Initial
        [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}], # Loop 1
        [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Blocked', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, '_read_file_for_context')
    @patch.object(WorkflowDriver, '_merge_snippet')
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', side_effect=Exception("Generic write error"))
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    # Add patch for builtins.open
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_handles_generic_write_file_exceptions(self,
                                                          mock_open, # Corresponds to @patch('builtins.open', ...)
                                                          mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                          mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                          mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                          mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                          mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                          mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                          mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                          mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                          mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                          mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                          mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                          test_driver_validation, tmp_path, mocker, caplog):
        """Test that autonomous_loop handles generic exceptions from _write_output_file gracefully."""
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        # FIX: Define task_list_not_started for assertions
        task_list_not_started = [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}]
        # ADDED: Define task_list_blocked for assertions
        task_list_blocked = [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Blocked', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}]


        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_not_called()
        mock_merge_snippet.assert_not_called()
        mock_invoke_coder_llm.assert_not_called()
        # Assert on the mock instances from the fixture
        mock_code_review_agent.analyze_python.assert_not_called()
        mock_ethical_governance_engine.enforce_policy.assert_not_called()

        # _write_output_file is called for both steps because target_file is set
        # Step 1 is file writing (non-code-gen), Step 2 is not file writing
        # Only Step 1 should call _write_output_file
        assert mock_write_output_file.call_count == 1 # Only called for Step 1
        # FIX: Assert overwrite=True based on the new code logic
        mock_write_output_file.assert_any_call("error.txt", ANY, overwrite=True)
        assert "Failed to write file error.txt: Generic write error" in caplog.text
        assert caplog.text.count("Failed to write file error.txt: Generic write error") == 1

        # The loop should now complete normally and log this message in the second iteration
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text # This assertion should now pass with the fix in workflow_driver.py
        step1_logs = "\n".join([log for log in caplog.text.splitlines() if "Step 1" in log])
        step2_logs = "\n".join([log for log in caplog.text.splitlines() if "Step 2" in log])
        # The step is identified as file writing, so this log should NOT appear for step 1
        # FIX: Corrected assertion to check for the *actual* log message
        assert "Step identified as explicit file writing. Processing file operation for step: Step 1: Write output to error.txt" in step1_logs
        # Step 2 IS NOT file writing, code gen, or test execution
        # FIX: Corrected assertion to check for the *actual* log message
        assert "Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: Step 2: Another step." in step2_logs

        # Status update should happen because of step errors
        # FIX: Assert that safe_write_roadmap was called once and check the status
        mock_safe_write_roadmap.assert_called_once()
        written_data = mock_safe_write_roadmap.call_args[0][1]
        assert written_data['tasks'][0]['status'] == 'Blocked'
        # ADDED: Assert the full content written matches the expected blocked state
        assert written_data == {'tasks': task_list_generic_error_blocked_expected_write}

        # ADDED: Assert that open was called to read the roadmap before writing the blocked status
        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')

        # ADDED: Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_blocked)

        # ADDED: Verify logging for status update
        assert 'Task task_generic_error marked as \'Blocked\' due to step execution errors.' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Blocked\' for task task_generic_error' in caplog.text
        assert 'Successfully wrote updated status for task task_generic_error in dummy_roadmap.json' in caplog.text


    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Add mock for builtins.open for status update read
    # FIX: Correct argument order in signature
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Not Started', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}], # Initial
        [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Not Started', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}], # Loop 1
        [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Completed', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Not Started', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}, # Select task
        None # No more tasks after the first one
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=[
        "Step 1: Implement feature and add logic to src/feature.py",
        "Step 2: Run pytest tests for src/feature.py"
    ])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing content.")
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'execute_tests', return_value=(0, "Pytest output", ""))
    @patch.object(WorkflowDriver, '_parse_test_results', return_value={'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1, 'message': 'Parsed successfully.'}) # Simulate parsed failure
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_calls_reporting_and_persistence(self,
                                                        mock_open,                     # Corresponds to @patch('builtins.open', ...)
                                                        mock_get_full_path,            # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                        mock_safe_write_roadmap,       # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                        mock_parse_and_evaluate,       # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                        mock_generate_report,          # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                        mock_parse_test_results,       # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results', ...)
                                                        mock_execute_tests,            # Corresponds to @patch.object(WorkflowDriver, 'execute_tests', ...)
                                                        mock_write_output_file,        # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                        mock_merge_snippet,            # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                        mock_invoke_coder_llm,         # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                        mock_read_file_for_context,    # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                        mock_generate_plan,            # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                        mock_select_next_task,         # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                        mock_load_roadmap,             # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                        test_driver_validation, caplog, tmp_path, mocker):
        """
        Test that autonomous_loop calls generate_grade_report, _parse_and_evaluate_grade_report,
        and _safe_write_roadmap_json after completing plan steps.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set return values on the mock instances from the fixture
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        # FIX: Define task_list_not_started and task_list_completed_expected_write for assertions
        task_list_not_started = [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Not Started', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}]
        # FIX: Corrected expected data for safe_write_roadmap_json assertion
        task_list_completed_expected_write = [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Completed', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}]


        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_called_once_with("src/feature.py")
        mock_invoke_coder_llm.assert_called_once()
        mock_merge_snippet.assert_called_once()
        mock_write_output_file.assert_called_once()

        # Assert on the mock instances from the fixture
        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_governance_engine.enforce_policy.call_count == 2
        calls = mock_ethical_governance_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write

        # The test command heuristic defaults to "tests/" if target_file doesn't look like a test file
        mock_execute_tests.assert_called_once_with(["pytest", "tests/"], driver.context.base_path)
        mock_parse_test_results.assert_called_once_with("Pytest output")

        mock_generate_report.assert_called_once()
        called_task_id = mock_generate_report.call_args[0][0]
        assert called_task_id == 'task_report_gen'

        called_results = mock_generate_report.call_args[0][1]
        assert isinstance(called_results, dict)
        assert 'test_results' in called_results
        assert 'code_review_results' in called_results
        assert 'ethical_analysis_results' in called_results
        assert 'step_errors' in called_results # Assert step_errors is included

        mock_parse_and_evaluate.assert_called_once_with(mock_generate_report.return_value)

        # Assert that open was called to read the roadmap before writing
        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')

        # safe_write_roadmap is called because the status changes to "Completed"
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, ANY)
        # Check the content passed to safe_write_roadmap
        written_data = mock_safe_write_roadmap.call_args[0][1]
        assert written_data == {'tasks': task_list_completed_expected_write} # Use the corrected expected data


        assert "Generating Grade Report..." in caplog.text
        assert f"--- GRADE REPORT for Task task_report_gen ---\n{mock_generate_report.return_value}\n--- END GRADE REPORT ---" in caplog.text
        assert "Grade Report Evaluation: Recommended Action='Completed'" in caplog.text # Check log from evaluation
        assert "Updating task status from 'Not Started' to 'Completed' for task task_report_gen" in caplog.text
        assert 'Successfully wrote updated status for task task_report_gen in dummy_roadmap.json' in caplog.text # Added assertion back
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text


    # --- NEW TESTS FOR TASK 1_6J INTEGRATION ---

    # FIX: Provide 3 return values for load_roadmap side_effect
    # FIX: Correct assertion for select_next_task call argument
    # FIX: Remove redundant patches and use fixture mocks
    # FIX: Correct argument order in signature
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}], # Initial load
        [{'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}], # Loop 1 load
        [{'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}] # Loop 2 load (after status update)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}, # Select task in loop 1
        None # No more tasks in loop 2
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement code in src/success.py", "Step 2: Run tests"])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="")
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="print('success')")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="print('success')")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'execute_tests', return_value=(0, "Pytest output", ""))
    @patch.object(WorkflowDriver, '_parse_test_results', return_value={'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1, 'message': 'Parsed successfully.'}) # Simulate parsed failure
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_success_flow(self,
                                mock_open, # Corresponds to @patch('builtins.open', ...)
                                mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                mock_parse_test_results, # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results', ...)
                                mock_execute_tests, # Corresponds to @patch.object(WorkflowDriver, 'execute_tests', ...)
                                mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                test_driver_validation, caplog, tmp_path, mocker):
        """
        Test Case 1: Successful task execution with code write, validation passing,
        and status update to "Completed".
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set return values on fixture mocks
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        # FIX: Define task_list_not_started and task_list_completed for assertions
        task_list_not_started = [{'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}]
        task_list_completed = [{'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()
        mock_read_file_for_context.assert_called_once_with("src/success.py")
        mock_invoke_coder_llm.assert_called_once()
        mock_merge_snippet.assert_called_once()
        mock_write_output_file.assert_called_once_with("src/success.py", ANY, overwrite=True)
        mock_execute_tests.assert_called_once_with(["pytest", "tests/"], driver.context.base_path)
        mock_parse_test_results.assert_called_once_with("Pytest output")
        mock_code_review_agent.analyze_python.assert_called_once_with(ANY)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_engine.enforce_policy.call_count == 2
        calls = mock_ethical_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write
        mock_generate_report.assert_called_once()
        mock_parse_and_evaluate.assert_called_once_with(ANY)
        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')
        # FIX: Use the corrected expected write data
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, {'tasks': task_list_success_completed_expected_write})

        # Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_completed)


        # Verify overall loop termination
        assert caplog.text.count('Starting autonomous loop iteration') == 2
        assert 'Selected task: ID=task_success' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Completed\' for task task_success' in caplog.text
        assert 'Successfully wrote updated status for task task_success in dummy_roadmap.json' in caplog.text # Added assertion back
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text

    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_fail_tests', 'task_name': 'Fail Tests Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/fail.py'}], # Initial
        [{'task_id': 'task_fail_tests', 'task_name': 'Fail Tests Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/fail.py'}], # Loop 1
        [{'task_id': 'task_fail_tests', 'task_name': 'Fail Tests Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/fail.py'}] # Loop 2 (status unchanged)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_fail_tests', 'task_name': 'Fail Tests Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/fail.py'}, # Select task
        None # No more tasks after the first one
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement code in src/fail.py", "Step 2: Run tests"])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="")
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="print('fail')")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="print('fail')")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'execute_tests', return_value=(1, "Pytest output", "Errors")) # Simulate test failure
    @patch.object(WorkflowDriver, '_parse_test_results', return_value={'status': 'failed', 'passed': 0, 'failed': 1, 'total': 1, 'message': 'Parsed successfully.'}) # Simulate parsed failure
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 95}, "validation_results": {"tests": {"status": "failed"}}})) # Simulate report with test failure
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Regenerate Code", "justification": "Automated tests failed."}) # Simulate evaluation recommending regenerate
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    # Add patch for builtins.open
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_tests_fail_regenerate_flow(self,
                                                    mock_open, # Corresponds to @patch('builtins.open', ...)
                                                    mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                    mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                    mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                    mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                    mock_parse_test_results, # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results', ...)
                                                    mock_execute_tests, # Corresponds to @patch.object(WorkflowDriver, 'execute_tests', ...)
                                                    mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                    mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                    mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                    mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                    mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                    mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                    mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                    test_driver_validation, caplog, tmp_path, mocker):
        """
        Test Case 2: Task execution with code write, tests failing, report evaluation
        recommending "Regenerate Code", status remains "Not Started".
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set return values on fixture mocks
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        # FIX: Define task_list_not_started for assertions
        task_list_not_started = [{'task_id': 'task_fail_tests', 'task_name': 'Fail Tests Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/fail.py'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()
        mock_write_output_file.assert_called_once_with("src/fail.py", ANY, overwrite=True)
        mock_code_review_agent.analyze_python.assert_called_once_with(ANY)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_engine.enforce_policy.call_count == 2
        calls = mock_ethical_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write
        mock_execute_tests.assert_called_once_with(["pytest", "tests/"], driver.context.base_path)
        mock_parse_test_results.assert_called_once_with("Pytest output")
        mock_generate_report.assert_called_once()
        mock_parse_and_evaluate.assert_called_once_with(ANY)

        # Verify roadmap status update was NOT called because status didn't change
        mock_safe_write_roadmap.assert_not_called()

        # Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_not_started) # Status is still Not Started


        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_fail_tests' in caplog.text
        assert 'Test Execution Results: Status=failed' in caplog.text
        assert 'Tests failed for step: Step 2: Run tests. Raw stderr:\nErrors' in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Regenerate Code\'' in caplog.text
        assert 'Task status for task_fail_tests remains \'Not Started\' based on evaluation.' in caplog.text
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text

    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py'}], # Initial
        [{'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py'}], # Loop 1
        [{'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py'}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py'}, # Select task
        None # No more tasks after the first one
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement code in src/ethical.py"])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="")
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="print('rejected')")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="print('rejected')")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'execute_tests') # Should not be called
    @patch.object(WorkflowDriver, '_parse_test_results') # Should not be called
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 0}, "validation_results": {"ethical_analysis": {"overall_status": "rejected"}}})) # Simulate report with ethical rejection
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Blocked", "justification": "Ethical analysis rejected the code."}) # Simulate evaluation recommending blocked
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_ethical_reject_blocked_flow(self,
                                                    mock_open, # Corresponds to @patch('builtins.open', ...)
                                                    mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                    mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                    mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                    mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                    mock_parse_test_results, # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results')
                                                    mock_execute_tests, # Corresponds to @patch.object(WorkflowDriver, 'execute_tests')
                                                    mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                    mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                    mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                    mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                    mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                    mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                    mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                    test_driver_validation, caplog, tmp_path, mocker):
        """
        Test Case 3: Task execution with code write, ethical analysis rejecting,
        report evaluation recommending "Blocked", status updates to "Blocked".
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set return values on fixture mocks
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_engine.enforce_policy.return_value = {'overall_status': 'rejected', 'policy_name': 'Mock Policy'} # Simulate rejection

        # FIX: Define task_list_not_started and task_list_blocked for assertions
        task_list_not_started = [{'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py'}]
        task_list_blocked = [{'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()
        # _write_output_file should NOT be called if pre-write ethical validation fails
        mock_write_output_file.assert_not_called()
        # Consequently, post-write code review and ethical analysis should also not be called
        mock_code_review_agent.analyze_python.assert_not_called()
        # Pre-write ethical check is called once with the raw snippet
        mock_ethical_engine.enforce_policy.assert_called_once_with(mock_invoke_coder_llm.return_value, driver.default_policy_config)
        mock_execute_tests.assert_not_called()
        mock_parse_test_results.assert_not_called()
        mock_generate_report.assert_called_once()
        mock_parse_and_evaluate.assert_called_once_with(ANY)
        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')
        # FIX: Use the corrected expected write data
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, {'tasks': task_list_ethical_blocked_expected_write})

        # Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_blocked)


        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_ethical_reject' in caplog.text
        assert "Pre-write ethical validation failed for snippet: {'overall_status': 'rejected', 'policy_name': 'Mock Policy'}" in caplog.text
        assert "Skipping write/merge." in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Blocked\'' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Blocked\' for task task_ethical_reject' in caplog.text
        assert 'Successfully wrote updated status for task task_ethical_reject in dummy_roadmap.json' in caplog.text # Added assertion back
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text

    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py'}], # Initial
        [{'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py'}], # Loop 1
        [{'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py'}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py'}, # Select task
        None # No more tasks after the first one
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement code in src/security.py"])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="")
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="import os; os.system('ls')")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="import os; os.system('ls')")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'execute_tests') # Should not be called
    @patch.object(WorkflowDriver, '_parse_test_results') # Should not be called
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 50}, "validation_results": {"code_review": {"static_analysis": [{"severity": "security_high"}]}}})) # Simulate report with high security finding
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Blocked", "justification": "High-risk security findings detected."}) # Simulate evaluation recommending blocked
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_security_high_blocked_flow(self,
                                                    mock_open, # Corresponds to @patch('builtins.open', ...)
                                                    mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                    mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                    mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                    mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                    mock_parse_test_results, # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results')
                                                    mock_execute_tests, # Corresponds to @patch.object(WorkflowDriver, 'execute_tests')
                                                    mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                    mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                    mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                    mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                    mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                    mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                    mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                    test_driver_validation, caplog, tmp_path, mocker):
        """
        Test Case 4: Task execution with code write, security scan finding high-risk issues,
        report evaluation recommending "Blocked", status updates to "Blocked".
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set return values on fixture mocks
        mock_code_review_agent.analyze_python.return_value = {'status': 'failed', 'static_analysis': [{'severity': 'security_high', 'code': 'B603', 'message': 'Subprocess used'}], 'errors': {'flake8': None, 'bandit': None}} # Simulate high security finding
        mock_ethical_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        # FIX: Define task_list_not_started and task_list_blocked for assertions
        task_list_not_started = [{'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py'}]
        task_list_blocked = [{'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()
        mock_write_output_file.assert_called_once_with("src/security.py", ANY, overwrite=True)
        mock_execute_tests.assert_not_called()
        mock_parse_test_results.assert_not_called()
        mock_code_review_agent.analyze_python.assert_called_once_with(ANY)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_engine.enforce_policy.call_count == 2
        calls = mock_ethical_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write
        mock_generate_report.assert_called_once()
        mock_parse_and_evaluate.assert_called_once_with(ANY)
        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')
        # FIX: Use the corrected expected write data
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, {'tasks': task_list_security_blocked_expected_write})

        # Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_blocked)


        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_security_high' in caplog.text
        assert 'Code Review and Security Scan Results for src/security.py: ' in caplog.text
        assert "'severity': 'security_high'" in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Blocked\'' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Blocked\' for task task_security_high' in caplog.text
        assert 'Successfully wrote updated status for task task_security_high in dummy_roadmap.json' in caplog.text # Added assertion back
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text

    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py'}], # Initial
        [{'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py'}], # Loop 1
        [{'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py'}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py'}, # Select task
        None # No more tasks after the first one
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement code in src/error.py", "Step 2: Run tests"])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="")
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="print('error')")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="print('error')")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, '_parse_test_results') # Should not be called if execute_tests fails
    # Apply the fix here: Change "tests" to "test_results" in the return_value dictionary
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 0}, "validation_results": {"test_results": {"status": "error"}, "code_review": {"status": "error"}, "ethical_analysis": {"overall_status": "error"}}})) # Simulate report with errors
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Overall grade (0%) is below regeneration threshold or other issues require manual review."}) # Simulate evaluation recommending manual review
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_validation_error_manual_review_flow(self,
                                                        mock_open, # Corresponds to @patch('builtins.open', ...)
                                                        mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                        mock_safe_write_roadmap, # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                        mock_parse_and_evaluate, # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                        mock_generate_report, # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                        mock_parse_test_results, # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results')
                                                        mock_write_output_file, # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                        mock_merge_snippet, # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                                        mock_invoke_coder_llm, # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                                        mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                                        mock_generate_plan, # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                        mock_select_next_task, # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                        mock_load_roadmap, # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                        test_driver_validation, caplog, tmp_path, mocker):
        """
        Test Case 5: Task execution with code write, validation steps encountering
        execution errors (e.g., subprocess fails), report evaluation recommending
        "Manual Review Required", status updates to "Blocked" due to step errors.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set return values on fixture mocks
        mock_code_review_agent.analyze_python.return_value = {'status': 'error', 'errors': {'flake8': 'Flake8 error', 'bandit': 'Bandit error'}} # Simulate code review error
        mock_ethical_engine.enforce_policy.return_value = {'overall_status': 'error', 'message': 'Ethical analysis failed.'} # Simulate ethical analysis error

        driver.roadmap_path = "dummy_roadmap.json"
        task_list_not_started = [{'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py'}]

        # Mock execute_tests to raise an exception
        mock_execute_tests = mocker.patch.object(driver, 'execute_tests', side_effect=Exception("Test execution failed"))

        # Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()
        mock_write_output_file.assert_called_once_with("src/error.py", ANY, overwrite=True)

        # Verify validation steps were attempted and logged errors
        mock_execute_tests.assert_called_once_with(["pytest", "tests/"], driver.context.base_path)
        # The log message comes from the inner except block
        assert "An unexpected error occurred during command execution: Test execution failed" in caplog.text
        mock_parse_test_results.assert_not_called()

        mock_code_review_agent.analyze_python.assert_called_once_with(ANY)
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_engine.enforce_policy.call_count == 2
        calls = mock_ethical_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write

        mock_generate_report.assert_called_once()
        report_args = mock_generate_report.call_args[0]
        assert report_args[0] == 'task_validation_error'
        # These assertions check the state populated by the inner except block
        assert report_args[1]['test_results']['status'] == 'error'
        assert report_args[1]['test_results']['message'] == 'Test execution failed' # Add this assertion
        assert report_args[1]['code_review_results']['status'] == 'error'
        assert report_args[1]['ethical_analysis_results']['overall_status'] == 'error'
        # These assertions check the state populated by the outer except block (after code change)
        assert len(report_args[1]['step_errors']) == 1 # Assert that step_errors is not empty
        assert report_args[1]['step_errors'][0]['error_type'] == 'Exception' # Check step error type
        assert report_args[1]['step_errors'][0]['step_index'] == 2 # Check step index (Step 2 is index 1, +1 = 2)


        mock_parse_and_evaluate.assert_called_once_with(ANY)

        # Verify roadmap status update WAS called because status changed to Blocked
        # FIX: Change assertion to expect the call with the updated status
        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r') # Called to read before writing
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, {'tasks': task_list_validation_error_blocked_expected_write})


        # Verify calls for the second loop iteration (no tasks found)
        # The task status is now 'Blocked', so select_next_task will return None
        mock_select_next_task.assert_any_call([{'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py'}])


        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_validation_error' in caplog.text
        assert 'Code Review and Security Scan Results for src/error.py: ' in caplog.text
        assert "'status': 'error'" in caplog.text
        assert 'Ethical Analysis Results for src/error.py: ' in caplog.text
        assert "'overall_status': 'error'" in caplog.text
        # The log message from the outer except block should now be present
        assert "Error executing step 2/2: Step 2: Run tests" in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Manual Review Required\'' in caplog.text
        # FIX: Assert the log message for status change to Blocked
        assert 'Task task_validation_error marked as \'Blocked\' due to step execution errors.' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Blocked\' for task task_validation_error' in caplog.text
        assert 'Successfully wrote updated status for task task_validation_error in dummy_roadmap.json' in caplog.text
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text

    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_non_code', 'task_name': 'Non Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}], # Initial
        [{'task_id': 'task_non_code', 'task_name': 'Non Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}], # Loop 1
        [{'task_id': 'task_non_code', 'task_name': 'Non Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}] # Loop 2 (status unchanged)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_non_code', 'task_name': 'Non Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}, # Select task
        None # No more tasks after the first one
    ])
    # --- FIX 2 APPLIED HERE ---
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Research topic X", "Step 2: Write file documentation.md"]) # Non-code steps
    @patch.object(WorkflowDriver, '_read_file_for_context')
    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    @patch.object(WorkflowDriver, '_merge_snippet')
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Mock write for documentation.md
    @patch.object(WorkflowDriver, 'execute_tests')
    @patch.object(WorkflowDriver, '_parse_test_results')
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 0}, "validation_results": {}})) # Simulate report with no results
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_non_code_step_skips_validation(self,
                                                    mock_open,                     # Corresponds to @patch('builtins.open', ...)
                                                    mock_get_full_path, # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                                    mock_safe_write_roadmap,       # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                                    mock_parse_and_evaluate,       # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                                    mock_generate_report,          # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                                    mock_parse_test_results,       # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results')
                                                    mock_execute_tests,            # Corresponds to @patch.object(WorkflowDriver, 'execute_tests')
                                                    mock_write_output_file,        # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                                    mock_merge_snippet,            # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet')
                                                    mock_invoke_coder_llm,         # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm')
                                                    mock_read_file_for_context, # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context')
                                                    mock_generate_plan,            # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                                    mock_select_next_task,         # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                                    mock_load_roadmap,             # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                                    test_driver_validation, caplog, tmp_path, mocker):
        """
        Test Case 6: Task execution with a plan step that does *not* involve code writing
        or file operations. Validation steps should be skipped for this step.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        # FIX: Define task_list_not_started for assertions
        task_list_not_started = [{'task_id': 'task_non_code', 'task_name': 'Non Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()

        # Verify that code generation/writing/validation steps were NOT called for the first step ("Research topic X")
        # FIX: Corrected assertion to check for the *new* log message
        assert "Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: Step 1: Research topic X" in caplog.text
        mock_read_file_for_context.assert_not_called()
        mock_invoke_coder_llm.assert_not_called()
        mock_merge_snippet.assert_not_called()
        # Step 2 is "Update documentation.md", which is an explicit file write step
        mock_write_output_file.assert_called_once_with("documentation.md", ANY, overwrite=True)
        mock_execute_tests.assert_not_called()
        mock_parse_test_results.assert_not_called()
        mock_code_review_agent.analyze_python.assert_not_called()
        mock_ethical_governance_engine.enforce_policy.assert_not_called()

        # Verify report generation and evaluation were called after all steps
        mock_generate_report.assert_called_once()
        mock_parse_and_evaluate.assert_called_once_with(ANY)

        # Verify roadmap status update was NOT called because status didn't change
        mock_safe_write_roadmap.assert_not_called()

        # Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_not_started) # Status still Not Started


        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_non_code' in caplog.text
        assert 'Executing step 1/2: Step 1: Research topic X' in caplog.text
        assert 'Executing step 2/2: Step 2: Write file documentation.md' in caplog.text # Updated log message due to step change
        assert "Step identified as explicit file writing. Processing file operation for step: Step 2: Write file documentation.md" in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Manual Review Required\'' in caplog.text
        assert 'Task status for task_non_code remains \'Not Started\' based on evaluation.' in caplog.text
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text

    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}], # Initial
        [{'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}], # Loop 1
        [{'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}, # Select task
        None # No more tasks after the first one
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=[
        "Step 1: Implement feature A in src/file1.py",
        "Step 2: Implement feature B in src/file2.py", # Note: target_file is only file1.py in task
        "Step 3: Run tests for file1.py",
        "Step 4: Run tests for file2.py"
    ])
    @patch.object(WorkflowDriver, '_read_file_for_context', side_effect=["Content 1", "Content 1"]) # Simulate reading file1 twice
    @patch.object(WorkflowDriver, '_invoke_coder_llm', side_effect=["def func1(): pass # Snippet 1", "def func2(): pass # Snippet 2"]) # Simulate generating two valid snippets
    @patch.object(WorkflowDriver, '_merge_snippet', side_effect=["Merged 1", "Merged 2"]) # Simulate merging two snippets
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Simulate successful writes
    @patch.object(WorkflowDriver, 'execute_tests', side_effect=[(0, "Test1 Output", ""), (0, "Test2 Output", "")]) # Simulate two test runs
    @patch.object(WorkflowDriver, '_parse_test_results', side_effect=[
        {'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1, 'message': 'Parsed successfully.'},
        {'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1, 'message': 'Parsed successfully.'}
    ])
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_multiple_code_steps(self,
                                            mock_open,                     # Corresponds to @patch('builtins.open', ...)
                                            mock_get_full_path,            # Corresponds to @patch.object(Context, 'get_full_path', ...)
                                            mock_safe_write_roadmap,       # Corresponds to @patch.object(WorkflowDriver, '_safe_write_roadmap_json', ...)
                                            mock_parse_and_evaluate,       # Corresponds to @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', ...)
                                            mock_generate_report,          # Corresponds to @patch.object(WorkflowDriver, 'generate_grade_report', ...)
                                            mock_parse_test_results,       # Corresponds to @patch.object(WorkflowDriver, '_parse_test_results', ...)
                                            mock_execute_tests,            # Corresponds to @patch.object(WorkflowDriver, 'execute_tests', ...)
                                            mock_write_output_file,        # Corresponds to @patch.object(WorkflowDriver, '_write_output_file', ...)
                                            mock_merge_snippet,            # Corresponds to @patch.object(WorkflowDriver, '_merge_snippet', ...)
                                            mock_invoke_coder_llm,         # Corresponds to @patch.object(WorkflowDriver, '_invoke_coder_llm', ...)
                                            mock_read_file_for_context,    # Corresponds to @patch.object(WorkflowDriver, '_read_file_for_context', ...)
                                            mock_generate_plan,            # Corresponds to @patch.object(WorkflowDriver, 'generate_solution_plan', ...)
                                            mock_select_next_task,         # Corresponds to @patch.object(WorkflowDriver, 'select_next_task', ...)
                                            mock_load_roadmap,             # Corresponds to @patch.object(WorkflowDriver, 'load_roadmap', ...)
                                            test_driver_validation, caplog, tmp_path, mocker):
        """
        Test Case 7: Task execution with multiple code writing steps in the plan.
        Verifies validation is triggered after each code writing step and status updates.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        # Set side effects on fixture mocks
        mock_code_review_agent.analyze_python.side_effect = [{'status': 'success'}, {'status': 'success'}]
        # Extend the side_effect list to have at least 4 items for 2 code steps (2 pre, 2 post)
        mock_ethical_governance_engine.enforce_policy.side_effect = [{'overall_status': 'approved'}, {'overall_status': 'approved'}, {'overall_status': 'approved'}, {'overall_status': 'approved'}]

        # FIX: Define task_list_not_started and task_list_completed for assertions
        task_list_not_started = [{'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}]
        task_list_completed = [{'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        mock_select_next_task.assert_any_call(task_list_not_started)
        mock_generate_plan.assert_called_once()

        # Verify read/generate/merge/write/validate sequence for Step 1 (src/file1.py)
        mock_read_file_for_context.assert_any_call("src/file1.py")
        # Check calls for Snippet 1
        mock_invoke_coder_llm.assert_any_call(ANY) # Prompt for Snippet 1
        mock_merge_snippet.assert_any_call("Content 1", "def func1(): pass # Snippet 1")
        mock_write_output_file.assert_any_call("src/file1.py", "Merged 1", overwrite=True)
        # Pre-write ethical check for Snippet 1
        mock_ethical_governance_engine.enforce_policy.assert_any_call("def func1(): pass # Snippet 1", driver.default_policy_config)
        # Post-write validations for Merged 1
        mock_code_review_agent.analyze_python.assert_any_call("Merged 1")
        mock_ethical_governance_engine.enforce_policy.assert_any_call("Merged 1", driver.default_policy_config)

        # Verify read/generate/merge/write/validate sequence for Step 2 (src/file1.py due to target_file priority)
        mock_read_file_for_context.assert_any_call("src/file1.py")
        # Check calls for Snippet 2
        mock_invoke_coder_llm.assert_any_call(ANY) # Prompt for Snippet 2
        mock_merge_snippet.assert_any_call("Content 1", "def func2(): pass # Snippet 2")
        mock_write_output_file.assert_any_call("src/file1.py", "Merged 2", overwrite=True)
        # Pre-write ethical check for Snippet 2
        mock_ethical_governance_engine.enforce_policy.assert_any_call("def func2(): pass # Snippet 2", driver.default_policy_config)
        # Post-write validations for Merged 2
        mock_code_review_agent.analyze_python.assert_any_call("Merged 2")
        mock_ethical_governance_engine.enforce_policy.assert_any_call("Merged 2", driver.default_policy_config)


        # Verify test execution calls for Step 3 and Step 4
        mock_execute_tests.assert_any_call(["pytest", "tests/"], driver.context.base_path)
        mock_execute_tests.assert_any_call(["pytest", "tests/"], driver.context.base_path)
        assert mock_execute_tests.call_count == 2

        mock_parse_test_results.assert_any_call("Test1 Output")
        mock_parse_test_results.assert_any_call("Test2 Output")
        assert mock_parse_test_results.call_count == 2
        # Ethical engine called 4 times (2 pre-write, 2 post-write)
        assert mock_ethical_governance_engine.enforce_policy.call_count == 4


        # Verify report generation and evaluation were called after all steps
        mock_generate_report.assert_called_once()
        mock_parse_and_evaluate.assert_called_once_with(ANY)

        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')
        # FIX: Use the corrected expected write data
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, {'tasks': task_list_multiple_code_completed_expected_write})

        # Verify calls for the second loop iteration (no tasks found)
        mock_select_next_task.assert_any_call(task_list_completed)

        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_multiple_code' in caplog.text
        assert 'Executing step 1/4: Step 1: Implement feature A in src/file1.py' in caplog.text
        assert 'Executing step 2/4: Step 2: Implement feature B in src/file2.py' in caplog.text
        # FIX: Corrected assertion to check for the *new* log message
        assert "Step identified as code generation for file src/file1.py. Orchestrating read-generate-merge-write." in caplog.text.split("Executing step 2/4")[1].split("Executing step 3/4")[0]
        assert 'Successfully wrote merged content to src/file1.py.' in caplog.text.split("Executing step 2/4")[1].split("Executing step 3/4")[0]
        assert 'Running code review and security scan for src/file1.py...' in caplog.text.split("Executing step 2/4")[1].split("Executing step 3/4")[0]
        assert 'Running ethical analysis for src/file1.py...' in caplog.text.split("Executing step 2/4")[1].split("Executing step 3/4")[0]
        assert 'Executing step 3/4: Step 3: Run tests for file1.py' in caplog.text
        assert 'Executing step 4/4: Step 4: Run tests for file2.py' in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Completed\'' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Completed\' for task task_multiple_code' in caplog.text
        assert 'Successfully wrote updated status for task task_multiple_code in dummy_roadmap.json' in caplog.text # Added assertion back
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text

    # --- NEW TESTS FOR TASK 1.8.1 BUG ---
    # FIX: Refactored to use mocker.patch instead of @patch decorators
    def test_autonomous_loop_conceptual_step_with_file_mention_skips_write(self,
                                                                       test_driver_validation, caplog, tmp_path, mocker):
        """
        Test that a conceptual plan step that mentions a file (like the first step of task_1_8_1)
        is correctly identified and skips file writing/agent invocation.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        # Refactor patches to use mocker.patch
        mock_invoke_coder_llm = mocker.patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
        mock_generate_plan = mocker.patch.object(WorkflowDriver, 'generate_solution_plan', return_value=[
            "Step 1: Analyze the logic in src/core/automation/workflow_driver.py", # Conceptual step mentioning the file
            "Step 2: Implement the fix in src/core/automation/workflow_driver.py" # Code generation step
        ])
        mock_select_next_task = mocker.patch.object(WorkflowDriver, 'select_next_task', side_effect=[
            {'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Not Started', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'},
            None # Exit after the first task
        ])
        mock_load_roadmap = mocker.patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
            [{'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Not Started', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'}], # Initial load
            [{'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Not Started', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'}], # Loop 1 load
            [{'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Completed', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'}] # Loop 2 load (after status update)
        ])
        mock_read_file_for_context = mocker.patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing content.")
        mock_merge_snippet = mocker.patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
        mock_write_output_file = mocker.patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Mock write for the second step
        mock_execute_tests = mocker.patch.object(WorkflowDriver, 'execute_tests') # Ensure this is NOT called
        mock_parse_test_results = mocker.patch.object(WorkflowDriver, '_parse_test_results') # Ensure this is NOT called
        mock_generate_report = mocker.patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}}))
        mock_parse_eval_report = mocker.patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed", "justification": "Mock evaluation"})
        mock_safe_write_roadmap_json = mocker.patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True) # Mock roadmap write
        mock_builtins_open = mocker.patch('builtins.open', new_callable=MagicMock)


        # Set return values on fixture mocks for the second step's validations
        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        # FIX: Define task_list_not_started and task_list_completed for assertions
        task_list_not_started = [{'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Not Started', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'}]
        task_list_completed = [{'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Completed', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'}]

        # FIX: Configure mock_open for json.load
        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        # The variable 'mock_builtins_open' holds the mock for 'builtins.open'.
        mock_builtins_open.return_value.__enter__.return_value = mock_file


        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        # Verify calls for the first loop iteration (task execution)
        # The parameter 'mock_select_next_task' holds the mock for 'select_next_task' (decorator 3)
        mock_select_next_task.assert_any_call(task_list_not_started)
        # The parameter 'mock_generate_plan' holds the mock for 'generate_solution_plan' (decorator 2)
        mock_generate_plan.assert_called_once()


        # --- Assertions for Step 1 (Conceptual) ---
        # FIX: Assert for the *new* log message indicating skipping directly in caplog.text
        assert "Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: Step 1: Analyze the logic in src/core/automation/workflow_driver.py" in caplog.text
        # Ensure no file operations or agent calls happened for Step 1
        # mock_read_file_for_context should only be called for Step 2
        # mock_invoke_coder_llm should only be called for Step 2
        # mock_merge_snippet should only be called for Step 2
        # mock_write_output_file should NOT be called for Step 1
        # We will assert its call count is 1 later (only for Step 2)
        # mock_code_review_agent.analyze_python should only be called for Step 2
        # mock_ethical_governance_engine.enforce_policy should only be called for Step 2
        mock_execute_tests.assert_not_called() # This mock corresponds to execute_tests (decorator 9)
        mock_parse_test_results.assert_not_called() # This mock corresponds to _parse_test_results (decorator 10)

        # --- Assertions for Step 2 (Code Generation) ---
        # FIX: Assert for the *new* log message indicating code generation directly in caplog.text
        assert "Step identified as code generation for file src/core/automation/workflow_driver.py. Orchestrating read-generate-merge-write." in caplog.text
        # Ensure file operations and agent calls happened for Step 2
        # mock_read_file_for_context corresponds to _read_file_for_context (decorator 5)
        mock_read_file_for_context.assert_called_once_with("src/core/automation/workflow_driver.py")
        # mock_invoke_coder_llm corresponds to _invoke_coder_llm (decorator 1)
        mock_invoke_coder_llm.assert_called_once()
        # mock_merge_snippet corresponds to _merge_snippet (decorator 6)
        mock_merge_snippet.assert_called_once()
        # mock_write_output_file corresponds to _write_output_file (decorator 8)
        mock_write_output_file.assert_called_once_with("src/core/automation/workflow_driver.py", mock_merge_snippet.return_value, overwrite=True)

        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value) # Using the correct mock's return value
        # Ethical check is called twice: pre-write (on snippet) and post-write (on merged content)
        assert mock_ethical_governance_engine.enforce_policy.call_count == 2
        calls = mock_ethical_governance_engine.enforce_policy.call_args_list
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config) # Pre-write
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config) # Post-write


        # Verify report generation and evaluation were called after all steps
        # mock_generate_report corresponds to generate_grade_report (decorator 11)
        mock_generate_report.assert_called_once()
        # mock_parse_eval_report corresponds to _parse_and_evaluate_grade_report (decorator 12)
        mock_parse_eval_report.assert_called_once_with(ANY)

        # Verify roadmap status update
        # mock_builtins_open is the mock for builtins.open (decorator 14)
        # FIX: The assertion should check for the call to read the roadmap *before* writing the status update.
        # The path used here is the one returned by the mocked get_full_path for the roadmap file.
        mock_builtins_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')
        # mock_safe_write_roadmap_json corresponds to _safe_write_roadmap_json (decorator 13)
        mock_safe_write_roadmap_json.assert_called_once_with(driver.roadmap_path, {'tasks': task_list_conceptual_completed_expected_write})

        # Verify calls for the second loop iteration (no tasks found)
        # mock_select_next_task corresponds to select_next_task (decorator 3)
        mock_select_next_task.assert_any_call(task_list_completed)

        # Verify overall loop termination and logging
        assert 'Selected task: ID=task_1_8_1' in caplog.text
        assert 'Grade Report Evaluation: Recommended Action=\'Completed\'' in caplog.text
        assert 'Updating task status from \'Not Started\' to \'Completed\' for task task_1_8_1' in caplog.text
        assert 'Successfully wrote updated status for task task_1_8_1 in dummy_roadmap.json' in caplog.text # Added assertion back
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text