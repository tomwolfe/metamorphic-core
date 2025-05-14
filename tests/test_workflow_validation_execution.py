# tests/test_workflow_validation_execution.py

import pytest
import subprocess
from src.core.automation.workflow_driver import WorkflowDriver, Context
import logging
from unittest.mock import MagicMock, patch, call, ANY
from src.core.agents.code_review_agent import CodeReviewAgent
from pathlib import Path # Import Path
from src.core.ethics.governance import EthicalGovernanceEngine
import json # <-- Added this import

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_validation(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:
        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        # Mock load_policy_from_json on the ethical engine instance
        mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        driver = WorkflowDriver(context)
        driver.llm_orchestrator = MagicMock() # Mock LLM orchestrator
        # Ensure the driver instance uses the mocked CodeReviewAgent and EthicalGovernanceEngine
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set for tests

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance
        }

class TestWorkflowValidationExecution:

    # --- Tests for execute_tests ---
    @patch('subprocess.run')
    def test_execute_tests_success(self, mock_subprocess_run, test_driver_validation, tmp_path, caplog):
        """Test execute_tests successfully runs a command."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        mock_result = MagicMock(stdout="Test passed\n", stderr="", returncode=0)
        mock_subprocess_run.return_value = mock_result
        test_command = ["echo", "hello"]
        cwd = str(tmp_path)

        return_code, stdout, stderr = driver.execute_tests(test_command, cwd)

        mock_subprocess_run.assert_called_once_with(
            test_command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False
        )
        assert return_code == 0
        assert stdout == "Test passed\n"
        assert stderr == ""
        assert f"Executing command: echo hello in directory: {cwd or 'current directory'}" in caplog.text
        assert "Command executed successfully. Return code: 0" in caplog.text
        assert "STDOUT:\nTest passed\n" in caplog.text
        assert "STDERR:\n" in caplog.text

    @patch('subprocess.run')
    def test_execute_tests_failure(self, mock_subprocess_run, test_driver_validation, tmp_path, caplog):
        """Test execute_tests handles a command that returns a non-zero exit code."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        mock_result = MagicMock(stdout="Some stdout\n", stderr="Test failed\n", returncode=1)
        mock_subprocess_run.return_value = mock_result
        test_command = ["false"]
        cwd = str(tmp_path)

        return_code, stdout, stderr = driver.execute_tests(test_command, cwd)

        mock_subprocess_run.assert_called_once_with(
            test_command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False
        )
        assert return_code == 1
        assert stdout == "Some stdout\n"
        assert stderr == "Test failed\n"
        assert "Command failed with return code: 1" in caplog.text
        assert "STDOUT:\nSome stdout\n" in caplog.text
        assert "STDERR:\nTest failed\n" in caplog.text

    @patch('subprocess.run', side_effect=FileNotFoundError("command not found"))
    def test_execute_tests_command_not_found(self, mock_subprocess_run, test_driver_validation, tmp_path, caplog):
        """Test execute_tests handles FileNotFoundError."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_validation['driver']
        test_command = ["nonexistent_command"]
        cwd = str(tmp_path)

        return_code, stdout, stderr = driver.execute_tests(test_command, cwd)

        mock_subprocess_run.assert_called_once_with(
            test_command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False
        )
        assert return_code == 127
        assert stdout == ""
        assert "Error: Command executable not found. Ensure 'nonexistent_command' is in your system's PATH." in stderr
        assert "Error: Command executable not found. Ensure 'nonexistent_command' is in your system's PATH." in caplog.text

    @patch('subprocess.run', side_effect=OSError("permission denied"))
    def test_execute_tests_os_error(self, mock_subprocess_run, test_driver_validation, tmp_path, caplog):
        """Test execute_tests handles OSError."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_validation['driver']
        test_command = ["ls"]
        cwd = str(tmp_path)

        return_code, stdout, stderr = driver.execute_tests(test_command, cwd)

        mock_subprocess_run.assert_called_once_with(
            test_command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False
        )
        assert return_code == 1
        assert stdout == ""
        assert "An unexpected error occurred during command execution: permission denied" in stderr
        assert "An unexpected error occurred during command execution: permission denied" in caplog.text

    @patch('subprocess.run', side_effect=Exception("unexpected error"))
    def test_execute_tests_generic_exception(self, mock_subprocess_run, test_driver_validation, tmp_path, caplog):
        """Test execute_tests handles generic exceptions."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_validation['driver']
        test_command = ["ls"]
        cwd = str(tmp_path)

        return_code, stdout, stderr = driver.execute_tests(test_command, cwd)

        mock_subprocess_run.assert_called_once_with(
            test_command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False
        )
        assert return_code == 1
        assert stdout == ""
        assert "An unexpected error occurred during command execution: unexpected error" in stderr
        assert "An unexpected error occurred during command execution: unexpected error" in caplog.text

    @patch('subprocess.run')
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    def test_execute_tests_invalid_cwd(self, mock_get_full_path, mock_subprocess_run, test_driver_validation, caplog):
        """Test execute_tests handles non-existent working directory."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_validation['driver']
        test_command = ["echo", "hello"]
        cwd = "/nonexistent/directory/12345"

        mock_subprocess_run.side_effect = FileNotFoundError(f"No such file or directory: '{cwd}'")

        return_code, stdout, stderr = driver.execute_tests(test_command, cwd)

        mock_subprocess_run.assert_called_once_with(
            test_command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False
        )
        assert return_code == 127
        assert stdout == ""
        assert "Error: Command executable not found. Ensure 'echo' is in your system's PATH." in stderr
        assert "Error: Command executable not found. Ensure 'echo' is in your system's PATH." in caplog.text


    # --- Tests for _parse_test_results ---
    def test_parse_test_results_success_all_passed(self, test_driver_validation, caplog):
        """Test _parse_test_results with output showing all tests passed."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        output = """
============================= test session starts ==============================
platform linux -- Python 3.11.0, pytest-8.0.0, pluggy-1.5.0
rootdir: /app
collected 5 items

tests/test_example.py::test_one PASSED                                   [ 20%]
tests/test_example.py::test_two PASSED                                   [ 40%]
tests/test_another.py::test_three PASSED                                 [ 60%]
tests/test_another.py::test_four PASSED                                  [ 80%]
tests/test_edge_cases.py::test_five PASSED                               [100%]

============================== 5 passed in 1.23s ===============================
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 5, 'failed': 0, 'total': 5, 'status': 'passed', 'message': 'Parsed successfully.'}
        assert "Parsed test results:" in caplog.text

    def test_parse_test_results_success_with_failures(self, test_driver_validation, caplog):
        """Test _parse_test_results with output showing some failures."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        output = """
============================= test session starts ==============================
platform linux -- Python 3.11.0, pytest-8.0.0, pluggy-1.5.0
rootdir: /app
collected 7 items

tests/test_example.py::test_one PASSED                                   [ 14%]
tests/test_example.py::test_two FAILED                                   [ 28%]
tests/test_another.py::test_three PASSED                                 [ 42%]
tests/test_another.py::test_four FAILED                                  [ 57%]
tests/test_edge_cases.py::test_five PASSED                               [ 71%]
tests/test_edge_cases.py::test_six SKIPPED                               [ 85%]
tests/test_errors.py::test_seven ERROR                                   [100%]

============================== 2 failed, 3 passed, 1 skipped, 1 error in 4.56s ==============================
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 3, 'failed': 2, 'total': 7, 'status': 'failed', 'message': 'Parsed successfully.'}
        assert "Parsed test results:" in caplog.text

    def test_parse_test_results_success_only_failures(self, test_driver_validation, caplog):
        """Test _parse_test_results with output showing only failures."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        output = """
============================= test session starts ==============================
platform linux -- Python 3.11.0, pytest-8.0.0, pluggy-1.5.0
rootdir: /app
collected 3 items

tests/test_example.py::test_one FAILED                                   [ 33%]
tests/test_example.py::test_two FAILED                                   [ 66%]
tests/test_another.py::test_three FAILED                                 [100%]

============================== 3 failed in 0.78s ===============================
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 0, 'failed': 3, 'total': 3, 'status': 'failed', 'message': 'Parsed successfully.'}
        assert "Parsed test results:" in caplog.text

    def test_parse_test_results_empty_output(self, test_driver_validation, caplog):
        """Test _parse_test_results with empty input string."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_validation['driver']
        output = ""
        results = driver._parse_test_results(output)
        assert results == {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Received empty output.'}
        assert "Received empty output for test results parsing." in caplog.text

    def test_parse_test_results_no_summary_line(self, test_driver_validation, caplog):
        """Test _parse_test_results with output missing the summary line."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_validation['driver']
        output = """
Some other output
without a summary line
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not find pytest summary lines in output.'}
        assert "Could not find pytest summary lines in output." in caplog.text

    def test_parse_test_results_malformed_summary_line(self, test_driver_validation, caplog):
        """Test _parse_test_results with a malformed summary line."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_validation['driver']
        output = """
============================= test session starts ==============================
============================== malformed summary line ==============================
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not parse test results output.'}
        assert "Could not parse any counts from summary line: ============================= test session starts ==============================" in caplog.text

    def test_parse_test_results_only_skipped(self, test_driver_validation, caplog):
        """Test _parse_test_results with output showing only skipped tests."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        output = """
============================= test session starts ==============================
============================== 3 skipped in 0.10s ==============================
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 0, 'failed': 0, 'total': 3, 'status': 'passed', 'message': 'Parsed successfully.'}
        assert "Parsed test results:" in caplog.text

    def test_parse_test_results_only_errors(self, test_driver_validation, caplog):
        """Test _parse_test_results with output showing only errors."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        output = """
============================= test session starts ==============================
============================== 2 error in 0.15s ==============================
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 0, 'failed': 0, 'total': 2, 'status': 'failed', 'message': 'Parsed successfully.'}
        assert "Parsed test results:" in caplog.text

    def test_parse_test_results_mixed_order(self, test_driver_validation, caplog):
        """Test _parse_test_results with counts in a different order."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_validation['driver']
        output = """
============================= test session starts ==============================
============================== 1 error, 2 failed, 3 passed, 4 skipped in 0.5s ==============================
"""
        results = driver._parse_test_results(output)
        assert results == {'passed': 3, 'failed': 2, 'total': 10, 'status': 'failed', 'message': 'Parsed successfully.'}
        assert "Parsed test results:" in caplog.text

    def test_parse_test_results_total_zero_with_counts(self, test_driver_validation, caplog):
        """Test _parse_test_results handles a case where parsed counts > 0 but total is somehow zero (defensive)."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_validation['driver']
        output_zero_sum = """
============================= test session starts ==============================
============================== 0 passed, 0 failed, 0 skipped, 0 error in 0.1s ==============================
"""
        results_zero_sum = driver._parse_test_results(output_zero_sum)
        assert results_zero_sum == {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not parse test results output.'}

    # --- Tests for orchestration of validation steps within autonomous_loop ---
    # These tests verify that the correct methods (execute_tests, _parse_test_results,
    # CodeReviewAgent.analyze_python, EthicalGovernanceEngine.enforce_policy) are called
    # at the appropriate times based on the plan step and successful file write.

    # Test that CodeReviewAgent.analyze_python and EthicalGovernanceEngine.enforce_policy are called after successful code write
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement feature and add logic to src/feature.py"])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_review_exec', 'task_name': 'Review Exec Test', 'status': 'Not Started', 'description': 'Test review execution flow.', 'priority': 'High', 'target_file': 'src/feature.py'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'task_review_exec', 'task_name': 'Review Exec Test', 'status': 'Not Started', 'description': 'Desc Review execution flow.', 'priority': 'High', 'target_file': 'src/feature.py'}])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing content.")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(WorkflowDriver, 'execute_tests') # Ensure this is NOT called
    @patch.object(WorkflowDriver, '_parse_test_results') # Ensure this is NOT called
    # The side_effect lambda here now correctly uses Path because it's imported
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Patch _write_output_file and make it return True
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({})) # Mock report generation
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"}) # Mock report evaluation
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True) # Mock roadmap write
    # Changed fixture name from test_driver_validation to test_driver_reporting
    def test_autonomous_loop_code_review_execution_flow(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_parse_test_results, mock_execute_tests, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver_validation, tmp_path, caplog):
        """
        Test that autonomous_loop calls CodeReviewAgent.analyze_python
        after a successful code write.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        mock_review_results = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_code_review_agent.analyze_python.return_value = mock_review_results

        mock_ethical_results = {'overall_status': 'approved', 'policy_name': 'Test Policy'}
        mock_ethical_governance_engine.enforce_policy.return_value = mock_ethical_results

        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_execute_tests.assert_not_called()
        mock_parse_test_results.assert_not_called()

        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        assert mock_ethical_governance_engine.enforce_policy.call_count == 2
        calls = mock_ethical_governance_engine.enforce_policy.call_args_list
        # Pre-write call
        assert calls[0] == call(mock_invoke_coder_llm.return_value, driver.default_policy_config)
        # Post-write call
        assert calls[1] == call(mock_merge_snippet.return_value, driver.default_policy_config)


        assert "Running code review and security scan for src/feature.py..." in caplog.text
        assert f"Code Review and Security Scan Results for src/feature.py: {mock_review_results}" in caplog.text
        assert "Running ethical analysis for src/feature.py..." in caplog.text
        assert f"Ethical Analysis Results for src/feature.py: {mock_ethical_governance_engine.enforce_policy.return_value}" in caplog.text


    # Test that ethical analysis is skipped if default policy is not loaded
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="def generated_code(): return True")
    @patch.object(WorkflowDriver, 'generate_solution_plan', return_value=["Step 1: Implement feature and add logic to src/feature.py"])
    @patch.object(WorkflowDriver, 'select_next_task', side_effect=[
        {'task_id': 'task_ethical_skipped', 'task_name': 'Ethical Skipped Test', 'status': 'Not Started', 'description': 'Test ethical skipped flow.', 'priority': 'High', 'target_file': 'src/feature.py'},
        None
    ])
    @patch.object(WorkflowDriver, 'load_roadmap', return_value=[{'task_id': 'task_ethical_skipped', 'task_name': 'Ethical Skipped Test', 'status': 'Not Started', 'description': 'Desc Ethical skipped flow.', 'priority': 'High', 'target_file': 'src/feature.py'}])
    @patch.object(WorkflowDriver, '_read_file_for_context', return_value="Existing content.")
    @patch.object(WorkflowDriver, '_merge_snippet', return_value="Merged content")
    @patch.object(WorkflowDriver, 'execute_tests') # Ensure this is NOT called
    @patch.object(WorkflowDriver, '_parse_test_results') # Ensure this is NOT called
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Patch _write_output_file and make it return True
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({})) # Mock report generation
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"}) # Mock report evaluation
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True) # Mock roadmap write
    def test_autonomous_loop_ethical_analysis_skipped_flow(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_parse_test_results, mock_execute_tests, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver_validation, tmp_path, caplog):
        """
        Test that autonomous_loop skips ethical analysis if default policy is not loaded.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_validation['driver']
        mock_code_review_agent = test_driver_validation['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_validation['mock_ethical_governance_engine']

        driver.default_policy_config = None # Explicitly set default_policy_config to None

        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}

        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_execute_tests.assert_not_called()
        mock_parse_test_results.assert_not_called()

        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        mock_ethical_governance_engine.enforce_policy.assert_not_called()

        assert "Running code review and security scan for src/feature.py..." in caplog.text
        assert "Default ethical policy not loaded. Skipping ethical analysis." in caplog.text