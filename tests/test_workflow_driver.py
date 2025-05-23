# File: tests/test_workflow_driver.py
import pytest
import html
import shutil
import subprocess

from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT, MAX_STEP_RETRIES
import os
import logging

from src.cli.write_file import write_file, file_exists
from pathlib import Path
import json
from unittest.mock import MagicMock, patch, ANY, call
import re

from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from datetime import datetime
import uuid
import builtins

if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(name)s - %(message)s')

logger = logging.getLogger(__name__)

MAX_READ_FILE_SIZE = 1024 * 1024
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"
MAX_STEP_RETRIES = 2

@pytest.fixture
def test_driver(tmp_path):
    context = Context(str(tmp_path))
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator:

        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value

        driver = WorkflowDriver(context)
        driver.llm_orchestrator = mock_llm_orchestrator_instance
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        driver.default_policy_config = {'policy_name': 'Mock Policy'}

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance,
            'mock_llm_orchestrator': mock_llm_orchestrator_instance
        }

@pytest.fixture
def test_driver_validation(tmp_path, mocker):
    mock_get_full_path = mocker.patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")

    context = Context(str(tmp_path))

    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator:

        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value

        mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        driver = WorkflowDriver(context)
        driver.llm_orchestrator = mock_llm_orchestrator_instance
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        driver.default_policy_config = {'policy_name': 'Mock Policy'}

        mock_get_full_path.reset_mock()

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance,
            'mock_get_full_path': mock_get_full_path
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

task_list_not_started = [{'task_id': 'mock_task', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}]
task_list_completed = [{'task_id': 'mock_task', 'task_name': 'Mock Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High'}]
task_list_blocked = [{'task_id': 'mock_task', 'task_name': 'Mock Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High'}]

task_list_completed_expected_write = [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Completed', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}]
task_list_success_completed_expected_write = [{'task_id': 'task_success', 'task_name': 'Success Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/success.py'}]
task_list_ethical_blocked_expected_write = [{'task_id': 'task_ethical_reject', 'task_name': 'Ethical Reject Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/ethical.py', 'reason_blocked': ANY}]
task_list_security_blocked_expected_write = [{'task_id': 'task_security_high', 'task_name': 'Security High Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/security.py', 'reason_blocked': ANY}]
task_list_multiple_code_completed_expected_write = [{'task_id': 'task_multiple_code', 'task_name': 'Multiple Code Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/file1.py'}]
task_list_conceptual_completed_expected_write = [{'task_id': 'task_1_8_1', 'task_name': 'Enhance Plan Step Identification', 'status': 'Completed', 'description': 'Improve step identification.', 'priority': 'Critical', 'target_file': 'src/core/automation/workflow_driver.py'}]
task_list_prioritize_target_completed_expected_write = [{'task_id': 'task_prioritize_target', 'task_name': 'Prioritize Target File', 'status': 'Completed', 'description': 'Test target file prioritization.', 'priority': 'High', 'target_file': 'correct/file_from_task.py'}]
task_list_validation_error_blocked_expected_write = [{'task_id': 'task_validation_error', 'task_name': 'Validation Error Task', 'status': 'Blocked', 'description': 'Desc', 'priority': 'High', 'target_file': 'src/error.py', 'reason_blocked': ANY}]
task_list_generic_error_blocked_expected_write = [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Blocked', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt', 'reason_blocked': ANY}]

class TestWorkflowDriver:
    # ... (other tests) ...

    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value=None)
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Write output to error.txt", "Step 2: Another step."])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'},
        None # Second call returns None to exit loop
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', side_effect=[
        [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}], # Initial
        [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}], # Loop 1
        [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Blocked', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt', 'reason_blocked': ANY}] # Loop 2 (after update)
    ])
    @patch.object(WorkflowDriver, '_read_file_for_context')
    @patch.object(WorkflowDriver, '_merge_snippet')
    @patch.object(WorkflowDriver, '_write_output_file', side_effect=Exception("Generic write error"))
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    @patch('builtins.open', new_callable=MagicMock)
    def test_autonomous_loop_handles_generic_write_file_exceptions(
                                                          self,
                                                          mock_open,
                                                          mock_safe_write_roadmap,
                                                          mock_parse_and_evaluate,
                                                          mock_generate_report,
                                                          mock_write_output_file,
                                                          mock_merge_snippet,
                                                          mock_read_file_for_context,
                                                          mock_load_roadmap,
                                                          mock_select_next_task,
                                                          mock_generate_plan,
                                                          mock_invoke_coder_llm,
                                                          test_driver_validation, tmp_path, mocker, caplog):
        """Test that autonomous_loop handles generic exceptions from _write_output_file gracefully."""
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']
        mock_get_full_path = test_driver_validation['mock_get_full_path']

        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Mock Policy'}

        task_list_not_started = [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}]
        task_list_blocked = [{'task_id': 'task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Blocked', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt', 'reason_blocked': ANY}]

        mock_file = MagicMock()
        mock_file.read.return_value = json.dumps({'tasks': task_list_not_started})
        mock_open.return_value.__enter__.return_value = mock_file

        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_not_called()
        mock_merge_snippet.assert_not_called()
        mock_invoke_coder_llm.assert_not_called()
        mock_code_review_agent.analyze_python.assert_not_called()
        mock_ethical_governance_engine.enforce_policy.assert_not_called()

        assert mock_write_output_file.call_count == MAX_STEP_RETRIES + 1
        mock_write_output_file.assert_any_call(mock_get_full_path("error.txt"), ANY, overwrite=True)

        # Assert the specific error log from line 1179 occurred MAX_STEP_RETRIES + 1 times
        error_log_count_write_failure = sum(
            1 for record in caplog.records
            if record.levelname == 'ERROR'
            and record.pathname.endswith('workflow_driver.py')
            and record.lineno == 1179 # Corrected line number
            and record.message == f"Failed to write file {mock_get_full_path('error.txt')}: Generic write error"
        )
        assert error_log_count_write_failure == MAX_STEP_RETRIES + 1

        # Assert the specific error log from line 1206 occurred MAX_STEP_RETRIES + 1 times
        error_log_count_step_failure = sum(
            1 for record in caplog.records
            if record.levelname == 'ERROR'
            and record.pathname.endswith('workflow_driver.py')
            and record.lineno == 1206 # Corrected line number
            and record.message.startswith("Step execution failed (Attempt")
            and record.message.endswith("Error: Generic write error")
        )
        assert error_log_count_step_failure == MAX_STEP_RETRIES + 1

        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text
        step1_logs = "\n".join([log for log in caplog.text.splitlines() if "Step 1" in log])
        step2_logs = "\n".join([log for log in caplog.text.splitlines() if "Step 2" in log])

        assert "Step identified as explicit file writing. Processing file operation for step: Step 1: Write output to error.txt" in step1_logs
        assert "Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: Step 2: Another step." not in step2_logs

        mock_safe_write_roadmap.assert_called_once()
        written_data = mock_safe_write_roadmap.call_args[0][1]
        assert written_data['tasks'][0]['status'] == 'Blocked'
        assert written_data == {'tasks': task_list_generic_error_blocked_expected_write}

        mock_open.assert_any_call('/resolved/dummy_roadmap.json', 'r')

        mock_select_next_task.assert_any_call(task_list_blocked)

        assert "Task task_generic_error marked as 'Blocked'." in caplog.text
        assert "Updating task status from 'Not Started' to 'Blocked' for task task_generic_error" in caplog.text
        assert "Successfully wrote updated status for task task_generic_error in dummy_roadmap.json" in caplog.text