# tests/test_workflow_driver.py

import pytest
import html
import shutil
import subprocess
from src.core.automation.workflow_driver import WorkflowDriver, Context
import os
import logging
from src.cli.write_file import write_file, file_exists
from pathlib import Path
import json
from unittest.mock import MagicMock, patch, ANY
import re
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from datetime import datetime
import uuid

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Define MAX_READ_FILE_SIZE here, matching the value in workflow_driver.py
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion, matching the value in workflow_driver.py
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"


@pytest.fixture
def test_driver(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation within the fixture setup
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:
        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        driver = WorkflowDriver(context)
        driver.llm_orchestrator = MagicMock()
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        driver.default_policy_config = {'policy_name': 'Mock Policy'}

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance
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

class TestWorkflowDriver:

    # --- Tests for start_workflow method ---
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_start_workflow_sets_attributes_and_calls_loop(self, mock_get_full_path, mock_load_roadmap, test_driver, tmp_path, mocker):
        """Test that start_workflow correctly sets attributes and calls autonomous_loop."""
        driver = test_driver['driver']
        mock_autonomous_loop = mocker.patch.object(driver, 'autonomous_loop')
        mock_context = Context(str(tmp_path))

        driver.start_workflow("path/to/roadmap.json", str(tmp_path / "output"), mock_context)

        assert driver.roadmap_path == "path/to/roadmap.json"
        assert driver.output_dir == str(tmp_path / "output")
        assert driver.context is mock_context

        mock_get_full_path.assert_called_once_with("path/to/roadmap.json")
        mock_load_roadmap.assert_called_once_with("/resolved/path/to/roadmap.json")
        mock_autonomous_loop.assert_called_once()

    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_start_workflow_with_empty_strings(self, mock_get_full_path, mock_load_roadmap, test_driver, tmp_path, mocker):
        """Test start_workflow handles empty string inputs."""
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

    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[])
    @patch.object(Context, 'get_full_path', return_value=None)
    def test_start_workflow_with_none(self, mock_get_full_path, mock_load_roadmap, test_driver, tmp_path, mocker, caplog):
        """Test start_workflow handles None roadmap_path gracefully (load fails internally, loop runs with empty tasks)."""
        caplog.set_level(logging.ERROR)
        driver = test_driver['driver']

        mock_autonomous_loop = mocker.patch.object(driver, 'autonomous_loop')
        mock_context_passed_in = Context(str(tmp_path))

        driver.start_workflow(None, None, mock_context_passed_in)

        assert driver.roadmap_path is None
        assert driver.output_dir is None

        mock_get_full_path.assert_called_once_with(None)
        mock_load_roadmap.assert_not_called()
        assert driver.tasks == []

        assert driver.context == mock_context_passed_in

        mock_autonomous_loop.assert_not_called()
        assert "Invalid roadmap path provided: None" in caplog.text

    # --- Tests for autonomous_loop orchestration ---
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_autonomous_loop_basic_logging(self, mock_get_full_path, mock_load_roadmap, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop logs the start and end messages when no tasks are available."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        driver.roadmap_path = "dummy_roadmap.json"

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        assert 'Starting autonomous loop iteration' in caplog.text
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text
        assert mock_load_roadmap.call_count == 2
        mock_load_roadmap.assert_any_call(f"/resolved/{driver.roadmap_path}")
        assert mock_get_full_path.call_count == 2
        mock_get_full_path.assert_any_call(driver.roadmap_path)


    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'},
        None
    ])
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=[])
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_autonomous_loop_task_selected_logging(self, mock_get_full_path, mock_load_roadmap, mock_generate_plan, mock_select_next_task, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop logs the selected task ID when a task is found and then exits."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        driver.roadmap_path = "dummy_roadmap.json"

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        assert mock_select_next_task.call_count == 2
        assert mock_load_roadmap.call_count == 3
        mock_load_roadmap.assert_any_call(f"/resolved/{driver.roadmap_path}")
        mock_select_next_task.assert_any_call(mock_load_roadmap.return_value)
        assert mock_get_full_path.call_count == 3
        mock_get_full_path.assert_any_call(driver.roadmap_path)


        assert 'Starting autonomous loop iteration' in caplog.text
        assert 'Selected task: ID=mock_task_1' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text


    @patch.object(WorkflowDriver, 'select_next_task', return_value=None)
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'mock_task_completed', 'task_name': 'Completed Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High'}])
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_autonomous_loop_no_task_logging(self, mock_get_full_path, mock_load_roadmap, mock_select_next_task, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop logs the 'No tasks available' message when no task is found."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        driver.roadmap_path = "dummy_roadmap.json"

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        mock_select_next_task.assert_called_once_with(mock_load_roadmap.return_value)
        assert mock_load_roadmap.call_count == 2
        mock_load_roadmap.assert_any_call(f"/resolved/{driver.roadmap_path}")
        assert mock_get_full_path.call_count == 2
        mock_get_full_path.assert_any_call(driver.roadmap_path)


        assert 'Starting autonomous loop iteration' in caplog.text
        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text


    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement feature and add logic to src/feature.py"])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'mock_task_code_write', 'task_name': 'Task Code Write', 'status': 'Not Started', 'description': 'Desc Code Write', 'priority': 'High', 'target_file': 'src/feature.py'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'mock_task_code_write', 'task_name': 'Task Code Write', 'status': 'Not Started', 'description': 'Desc Code Write', 'priority': 'High', 'target_file': 'src/feature.py'}])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    def test_autonomous_loop_calls_write_file_with_generated_content(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop calls _write_output_file with generated content when step is code gen + file write."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        mock_code_review_agent = test_driver['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver['mock_ethical_governance_engine']

        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Test Policy'}

        driver.roadmap_path = "dummy_roadmap.json"

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_called_once_with("src/feature.py")
        mock_invoke_coder_llm.assert_called_once()
        called_prompt = mock_invoke_coder_llm.call_args[0][0]
        assert "You are a Coder LLM expert in Python." in called_prompt
        assert "Overall Task: \"Task Code Write\"" in called_prompt
        assert "Specific Plan Step:\nStep 1: Implement feature and add logic to src/feature.py" in called_prompt
        assert "EXISTING CONTENT OF `src/feature.py`:\n```python\n\n```" in called_prompt

        mock_merge_snippet.assert_called_once_with(mock_read_file_for_context.return_value, mock_invoke_coder_llm.return_value)
        mock_write_output_file.assert_called_once_with("src/feature.py", mock_merge_snippet.return_value, overwrite=True)

        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(mock_merge_snippet.return_value, driver.default_policy_config)

        assert "Step identified as code generation for file src/feature.py. Orchestrating read-generate-merge-write." in caplog.text
        assert "Successfully wrote merged content to src/feature.py." in caplog.text
        assert "Running code review and security scan for src/feature.py..." in caplog.text
        assert "Running ethical analysis for src/feature.py..." in caplog.text


    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement feature and add logic to src/feature.py"])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'mock_task_code_write_exists', 'task_name': 'Task Code Write Exists', 'status': 'Not Started', 'description': 'Desc Code Write Exists', 'priority': 'High', 'target_file': 'src/feature.py'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'mock_task_code_write_exists', 'task_name': 'Task Code Write Exists', 'status': 'Not Started', 'description': 'Desc Code Write Exists', 'priority': 'High', 'target_file': 'src/feature.py'}])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing file content")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    def test_autonomous_loop_reads_existing_file_content(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver, caplog, tmp_path, mocker):
        """Test that autonomous_loop reads existing file content and includes it in the LLM prompt."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        mock_code_review_agent = test_driver['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver['mock_ethical_governance_engine']

        def get_full_path_side_effect(path):
            if path == "dummy_roadmap.json": # FIX: Use string literal instead of accessing driver.roadmap_path before it's set
                return f"/resolved/{path}"
            elif path == "src/feature.py":
                return "/app/src/feature.py"
            elif path == "policies/policy_bias_risk_strict.json":
                 return "/app/policies/policy_bias_risk_strict.json"
            return None

        mock_get_full_path_internal = mocker.patch.object(Context, 'get_full_path', side_effect=get_full_path_side_effect)

        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Test Policy'}

        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_called_once_with("src/feature.py")

        mock_invoke_coder_llm.assert_called_once()
        called_prompt = mock_invoke_coder_llm.call_args[0][0]

        assert "You are a Coder LLM expert in Python." in called_prompt
        assert "Overall Task: \"Task Code Write Exists\"" in called_prompt
        assert "Specific Plan Step:\nStep 1: Implement feature and add logic to src/feature.py" in called_prompt
        assert "EXISTING CONTENT OF `src/feature.py`:\n```python\nExisting file content\n```" in called_prompt

        mock_merge_snippet.assert_called_once_with(mock_read_file_for_context.return_value, mock_invoke_coder_llm.return_value)
        mock_write_output_file.assert_called_once_with("src/feature.py", mock_merge_snippet.return_value, overwrite=True)

        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(mock_merge_snippet.return_value, driver.default_policy_config)

        assert "Step identified as code generation for file src/feature.py. Orchestrating read-generate-merge-write." in caplog.text
        assert "Successfully wrote merged content to src/feature.py." in caplog.text
        assert "Running code review and security scan for src/feature.py..." in caplog.text
        assert "Running ethical analysis for src/feature.py..." in caplog.text


    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value=None)
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Write output to error.txt", "Step 2: Another step."])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'mock_task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'mock_task_generic_error', 'task_name': 'Task Generic Error', 'status': 'Not Started', 'description': 'Desc Generic Error', 'priority': 'High', 'target_file': 'error.txt'}])
    @patch.object(WorkflowDriver, '_read_file_for_context')
    @patch.object(WorkflowDriver, '_merge_snippet')
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', side_effect=Exception("Generic write error"))
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    # Changed fixture name from test_driver_validation to test_driver
    def test_autonomous_loop_handles_generic_write_file_exceptions(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver, tmp_path, mocker, caplog):
        """Test that autonomous_loop handles generic exceptions from _write_output_file gracefully."""
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        mock_code_review_agent = test_driver['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver['mock_ethical_governance_engine']

        driver.roadmap_path = "dummy_roadmap.json"

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_not_called()
        mock_merge_snippet.assert_not_called()
        mock_invoke_coder_llm.assert_not_called()
        mock_code_review_agent.analyze_python.assert_not_called()
        mock_ethical_governance_engine.enforce_policy.assert_not_called()

        assert mock_write_output_file.call_count == 2
        mock_write_output_file.assert_any_call("error.txt", ANY, overwrite=False)
        assert "Failed to write file error.txt: Generic write error" in caplog.text

        assert 'No tasks available in Not Started status. Exiting autonomous loop.' in caplog.text
        assert 'Autonomous loop terminated.' in caplog.text
        step1_logs = "\n".join([log for log in caplog.text.splitlines() if "Step 1" in log])
        assert "Step not identified as code generation or file writing." not in step1_logs


    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=[
        "Step 1: Implement feature and add logic to src/feature.py",
        "Step 2: Run pytest tests for src/feature.py"
    ])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Not Started', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Not Started', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing content.")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(WorkflowDriver, 'execute_tests', return_value=(0, "Pytest output", ""))
    @patch.object(WorkflowDriver, '_parse_test_results', return_value={'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1, 'message': 'Parsed successfully.'})
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True)
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}}))
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed", "justification": "Mock evaluation"})
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True)
    def test_autonomous_loop_calls_reporting_and_persistence(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_parse_test_results, mock_execute_tests, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver, tmp_path, mocker, caplog):
        """
        Test that autonomous_loop calls generate_grade_report, _parse_and_evaluate_grade_report,
        and _safe_write_roadmap_json after completing plan steps.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver['driver']
        mock_code_review_agent = test_driver['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver['mock_ethical_governance_engine']

        original_roadmap_data = [{'task_id': 'task_report_gen', 'task_name': 'Report Gen Test', 'status': 'Not Started', 'description': 'Test report generation flow.', 'priority': 'High', 'target_file': 'src/feature.py'}]
        mock_open = mocker.patch('builtins.open', new_callable=mocker.mock_open, read_data=json.dumps({'tasks': original_roadmap_data}))

        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_ethical_governance_engine.enforce_policy.return_value = {'overall_status': 'approved', 'policy_name': 'Test Policy'}

        driver.roadmap_path = "dummy_roadmap.json"

        driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        mock_read_file_for_context.assert_called_once_with("src/feature.py")
        mock_invoke_coder_llm.assert_called_once()
        mock_merge_snippet.assert_called_once()
        mock_write_output_file.assert_called_once()
        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(mock_merge_snippet.return_value, driver.default_policy_config)

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

        mock_parse_and_evaluate.assert_called_once_with(mock_generate_report.return_value)
        mock_safe_write_roadmap.assert_called_once()
        mock_safe_write_roadmap.assert_called_once_with(driver.roadmap_path, ANY)

        assert "Generating Grade Report..." in caplog.text
        assert f"--- GRADE REPORT for Task task_report_gen ---\n{mock_generate_report.return_value}\n--- END GRADE REPORT ---" in caplog.text
        # assert "Parsing and evaluating Grade Report..." in caplog.text # FIX: Remove assertion on log inside mocked method
        assert f"Grade Report Evaluation: Recommended Action='{mock_parse_and_evaluate.return_value['recommended_action']}', Justification='{mock_parse_and_evaluate.return_value['justification']}'" in caplog.text