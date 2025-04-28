# tests/test_workflow_reporting.py

import pytest
import json
from src.core.automation.workflow_driver import WorkflowDriver, Context
import logging
from unittest.mock import MagicMock, patch
from datetime import datetime

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_reporting(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation as they are not needed for reporting tests
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'):
        driver = WorkflowDriver(context)
        # driver.llm_orchestrator = MagicMock() # Not needed for these tests
        yield driver

class TestWorkflowReporting:

    # --- Tests for generate_grade_report ---
    def test_generate_grade_report(self, test_driver_reporting):
        driver = test_driver_reporting
        task_id = "test_task_1"
        mock_validation_results = {
            'test_results': {'status': 'passed', 'passed': 10, 'failed': 0, 'total': 10, 'message': 'Parsed successfully.'},
            'code_review_results': {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}},
            'ethical_analysis_results': {'overall_status': 'approved', 'policy_name': 'Strict Bias Risk Policy'},
        }
        # Mock _calculate_grades to return a predictable grade structure
        mock_grades = {
            "non_regression": {"percentage": 100, "justification": "Mock"},
            "test_success": {"percentage": 100, "justification": "Mock"},
            "code_style": {"percentage": 100, "justification": "Mock"},
            "ethical_policy": {"percentage": 100, "justification": "Mock"},
            "security_soundness": {"percentage": 100, "justification": "Mock"},
            "overall_percentage_grade": 100
        }
        with patch.object(driver, '_calculate_grades', return_value=mock_grades) as mock_calculate:
            report_json = driver.generate_grade_report(task_id, mock_validation_results)

            mock_calculate.assert_called_once_with(mock_validation_results)

            report_data = json.loads(report_json)

            assert report_data["task_id"] == task_id
            assert "timestamp" in report_data
            assert isinstance(report_data["validation_results"], dict)
            # FIX: Assert the structure matches how the method actually builds the dict
            assert report_data["validation_results"] == {
                "tests": mock_validation_results.get('test_results', {}),
                "code_review": mock_validation_results.get('code_review_results', {}),
                "ethical_analysis": mock_validation_results.get('ethical_analysis_results', {})}
            assert report_data["grades"] == mock_grades # Should contain the calculated grades

    # --- Tests for _calculate_grades ---

    def test__calculate_grades_all_pass(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            'test_results': {'status': 'passed', 'passed': 10, 'failed': 0, 'total': 10, 'message': 'Parsed successfully.'},
            'code_review_results': {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}},
            'ethical_analysis_results': {'overall_status': 'approved', 'policy_name': 'Strict Bias Risk Policy'},
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 100
        assert grades['code_style']['percentage'] == 100
        assert grades['ethical_policy']['percentage'] == 100
        assert grades['security_soundness']['percentage'] == 100
        assert grades['non_regression']['percentage'] == 100
        assert grades['overall_percentage_grade'] == 100

    def test__calculate_grades_tests_fail(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            'test_results': {'status': 'failed', 'passed': 5, 'failed': 5, 'total': 10, 'message': 'Parsed successfully.'},
            'code_review_results': {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}},
            'ethical_analysis_results': {'overall_status': 'approved', 'policy_name': 'Strict Bias Risk Policy'},
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 50
        assert grades['code_style']['percentage'] == 100
        assert grades['ethical_policy']['percentage'] == 100
        assert grades['security_soundness']['percentage'] == 100
        assert grades['non_regression']['percentage'] == 0
        assert grades['overall_percentage_grade'] == 65

    def test__calculate_grades_code_style_issues(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            'test_results': {'status': 'passed', 'passed': 10, 'failed': 0, 'total': 10, 'message': 'Parsed successfully.'},
            'code_review_results': {
                'status': 'failed',
                'static_analysis': [
                    {'severity': 'error', 'code': 'E001', 'message': 'Issue 1'},
                    {'severity': 'warning', 'code': 'W001', 'message': 'Issue 2'},
                    {'severity': 'style', 'code': 'C001', 'message': 'Issue 3'},
                    {'severity': 'info', 'code': 'D001', 'message': 'Issue 4'},
                ],
                'errors': {'flake8': None, 'bandit': None}
            },
            'ethical_analysis_results': {'overall_status': 'approved', 'policy_name': 'Strict Bias Risk Policy'},
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 100
        assert grades['code_style']['percentage'] == 64
        assert grades['ethical_policy']['percentage'] == 100
        assert grades['security_soundness']['percentage'] == 100
        assert grades['non_regression']['percentage'] == 100
        assert grades['overall_percentage_grade'] == 96

    def test__calculate_grades_ethical_violation(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            'test_results': {'status': 'passed', 'passed': 10, 'failed': 0, 'total': 10, 'message': 'Parsed successfully.'},
            'code_review_results': {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}},
            'ethical_analysis_results': {'overall_status': 'rejected', 'policy_name': 'Strict Bias Risk Policy', 'BiasRisk': {'status': 'violation'}},
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 100
        assert grades['code_style']['percentage'] == 100
        assert grades['ethical_policy']['percentage'] == 0
        assert grades['security_soundness']['percentage'] == 100
        assert grades['non_regression']['percentage'] == 100
        assert grades['overall_percentage_grade'] == 80

    def test__calculate_grades_security_violation_high(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            'test_results': {'status': 'passed', 'passed': 10, 'failed': 0, 'total': 10, 'message': 'Parsed successfully.'},
            'code_review_results': {
                'status': 'failed',
                'static_analysis': [
                    {'severity': 'security_high', 'code': 'B603', 'message': 'Subprocess used'}
                ],
                'errors': {'flake8': None, 'bandit': None}
            },
            'ethical_analysis_results': {'overall_status': 'approved', 'policy_name': 'Strict Bias Risk Policy'},
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 100
        assert grades['code_style']['percentage'] == 100
        assert grades['security_soundness']['percentage'] == 50
        assert grades['ethical_policy']['percentage'] == 100
        assert grades['non_regression']['percentage'] == 100
        assert grades['overall_percentage_grade'] == 90

    def test__calculate_grades_missing_results(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            # Missing test_results, code_review_results, ethical_analysis_results
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 0
        assert "No test results available." in grades['test_success']['justification']
        assert grades['code_style']['percentage'] == 0
        assert "No code review results available." in grades['code_style']['justification']
        assert grades['ethical_policy']['percentage'] == 0
        assert "No ethical analysis results available." in grades['ethical_policy']['justification']
        assert grades['security_soundness']['percentage'] == 0
        assert "No security results available." in grades['security_soundness']['justification']
        assert grades['non_regression']['percentage'] == 0
        assert grades['overall_percentage_grade'] == 0

    def test__calculate_grades_execution_errors(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            'test_results': {'status': 'error', 'message': 'Test execution failed.'},
            'code_review_results': {'status': 'error', 'errors': {'flake8': 'Flake8 error', 'bandit': 'Bandit error'}},
            'ethical_analysis_results': {'overall_status': 'error', 'message': 'Ethical analysis failed.'},
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 0
        assert "Test execution or parsing error: Test execution failed." in grades['test_success']['justification']
        assert grades['code_style']['percentage'] == 0
        assert "Code review/security execution error: Flake8 error, Bandit error" in grades['code_style']['justification']
        assert grades['ethical_policy']['percentage'] == 0
        assert "Ethical analysis execution error: Ethical analysis failed." in grades['ethical_policy']['justification']
        assert grades['security_soundness']['percentage'] == 0
        assert "Code review/security execution error: Flake8 error, Bandit error" in grades['security_soundness']['justification']
        assert grades['non_regression']['percentage'] == 0
        assert grades['overall_percentage_grade'] == 0

    def test__calculate_grades_ethical_skipped(self, test_driver_reporting):
        driver = test_driver_reporting
        mock_validation_results = {
            'test_results': {'status': 'passed', 'passed': 10, 'failed': 0, 'total': 10, 'message': 'Parsed successfully.'},
            'code_review_results': {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}},
            'ethical_analysis_results': {'overall_status': 'skipped', 'message': 'Default policy not loaded.'},
        }
        grades = driver._calculate_grades(mock_validation_results)

        assert grades['test_success']['percentage'] == 100
        assert grades['code_style']['percentage'] == 100
        assert grades['ethical_policy']['percentage'] == 0
        assert "Ethical analysis skipped: Default policy not loaded." in grades['ethical_policy']['justification']
        assert grades['security_soundness']['percentage'] == 100
        assert grades['non_regression']['percentage'] == 100
        assert grades['overall_percentage_grade'] == 80

    # --- Tests for _parse_and_evaluate_grade_report ---
    def test_parse_and_evaluate_grade_report_completed(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report returns 'Completed' for 100% grade."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 100},
            "validation_results": {
                "tests": {"status": "passed"},
                "code_review": {"status": "success", "static_analysis": []},
                "ethical_analysis": {"overall_status": "approved"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Completed"
        assert result["justification"] == "Overall grade is 100%."

    def test_parse_and_evaluate_grade_report_blocked_ethical(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report returns 'Blocked' for ethical rejection."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 70},
            "validation_results": {
                "tests": {"status": "passed"},
                "code_review": {"status": "success", "static_analysis": []},
                "ethical_analysis": {"overall_status": "rejected"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Blocked"
        assert result["justification"] == "Ethical analysis rejected the code."

    def test_parse_and_evaluate_grade_report_blocked_security(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report returns 'Blocked' for high-risk security."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 70},
            "validation_results": {
                "tests": {"status": "passed"},
                "code_review": {"status": "failed", "static_analysis": [{"severity": "security_high", "code": "B101"}]},
                "ethical_analysis": {"overall_status": "approved"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Blocked"
        assert result["justification"] == "High-risk security findings detected."

    def test_parse_and_evaluate_grade_report_regenerate_tests_failed(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report returns 'Regenerate Code' for test failures."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 95},
            "validation_results": {
                "tests": {"status": "failed", "passed": 5, "failed": 5, "total": 10},
                "code_review": {"status": "success", "static_analysis": []},
                "ethical_analysis": {"overall_status": "approved"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Regenerate Code"
        assert result["justification"] == "Automated tests failed."

    def test_parse_and_evaluate_grade_report_regenerate_grade_below_100_above_80(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report returns 'Regenerate Code' for grade >= 80 but < 100."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 85},
            "validation_results": {
                "tests": {"status": "passed"},
                "code_review": {"status": "failed", "static_analysis": [{"severity": "error", "code": "E001"}]},
                "ethical_analysis": {"overall_status": "approved"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Regenerate Code"
        assert result["justification"] == "Overall grade (85%) is below 100% but meets regeneration threshold."

    def test_parse_and_evaluate_grade_report_manual_review_grade_below_80(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report returns 'Manual Review Required' for grade < 80."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 79},
            "validation_results": {
                "tests": {"status": "passed"},
                "code_review": {"status": "failed", "static_analysis": [{"severity": "error", "code": "E001"}]},
                "ethical_analysis": {"overall_status": "approved"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Manual Review Required"
        assert result["justification"] == "Overall grade (79%) is below regeneration threshold or other issues require manual review."

    def test_parse_and_evaluate_grade_report_json_decode_error(self, test_driver_reporting, caplog):
        """Test _parse_and_evaluate_grade_report handles invalid JSON input."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_reporting
        invalid_json = "{ not valid json }"
        result = driver._parse_and_evaluate_grade_report(invalid_json)
        assert result["recommended_action"] == "Manual Review Required"
        assert "Failed to parse Grade Report JSON:" in result["justification"]
        assert "Failed to parse Grade Report JSON:" in caplog.text

    def test_parse_and_evaluate_grade_report_missing_keys(self, test_driver_reporting, caplog):
        """Test _parse_and_evaluate_grade_report handles missing keys gracefully."""
        caplog.set_level(logging.INFO)
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            # Missing 'grades' and 'validation_results' keys
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Manual Review Required"
        assert "Overall grade (0%) is below regeneration threshold or other issues require manual review." in result["justification"]
        assert "Grade Report Metrics: Overall Grade=0%, Test Status=None, Ethical Status=None, Code Review Status=None" in caplog.text

    def test_parse_and_evaluate_grade_report_ethical_error(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report handles ethical analysis error."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "tests": {"status": "passed"},
                "code_review": {"status": "success", "static_analysis": []},
                "ethical_analysis": {"overall_status": "error", "message": "Analysis failed"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Regenerate Code"
        assert "Overall grade (90%) is below 100% but meets regeneration threshold." in result["justification"]

    def test_parse_and_evaluate_grade_report_security_error(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report handles code review/security error."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "tests": {"status": "error", "errors": {"bandit": "Scan failed"}}, # FIX: Changed status to error and added errors key
                "code_review": {"status": "error", "errors": {"bandit": "Scan failed"}}, # FIX: Changed status to error and added errors key
                "ethical_analysis": {"overall_status": "approved"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Regenerate Code"
        assert "Overall grade (90%) is below 100% but meets regeneration threshold." in result["justification"]

    def test_parse_and_evaluate_grade_report_test_error(self, test_driver_reporting):
        """Test _parse_and_evaluate_grade_report handles test execution/parsing error."""
        driver = test_driver_reporting
        report_json = json.dumps({
            "task_id": "test_task",
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "tests": {"status": "error", "message": "Execution failed"},
                "code_review": {"status": "success", "static_analysis": []},
                "ethical_analysis": {"overall_status": "approved"}
            }
        })
        result = driver._parse_and_evaluate_grade_report(report_json)
        assert result["recommended_action"] == "Regenerate Code"
        assert "Overall grade (90%) is below 100% but meets regeneration threshold." in result["justification"]

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
    @patch.object(Context, 'get_full_path', side_effect=lambda path: str(Path("/resolved") / path) if path else "/resolved/")
    @patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Patch _write_output_file and make it return True
    @patch.object(WorkflowDriver, 'generate_grade_report', return_value=json.dumps({})) # Mock report generation
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Manual Review Required", "justification": "Mock evaluation"}) # Mock report evaluation
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json', return_value=True) # Mock roadmap write
    # Changed fixture name from test_driver_validation to test_driver_reporting
    def test_autonomous_loop_code_review_execution_flow(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_parse_test_results, mock_execute_tests, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver_reporting, tmp_path, caplog):
        """
        Test that autonomous_loop calls CodeReviewAgent.analyze_python
        after a successful code write.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_reporting['driver']
        mock_code_review_agent = test_driver_reporting['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_reporting['mock_ethical_governance_engine']

        mock_review_results = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}
        mock_code_review_agent.analyze_python.return_value = mock_review_results

        mock_ethical_results = {'overall_status': 'approved', 'policy_name': 'Test Policy'}
        mock_ethical_governance_engine.enforce_policy.return_value = mock_ethical_results

        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_execute_tests.assert_not_called()
        mock_parse_test_results.assert_not_called()

        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        mock_ethical_governance_engine.enforce_policy.assert_called_once_with(mock_merge_snippet.return_value, driver.default_policy_config)

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
    # Changed fixture name from test_driver_validation to test_driver_reporting
    def test_autonomous_loop_ethical_analysis_skipped_flow(self, mock_safe_write_roadmap, mock_parse_and_evaluate, mock_generate_report, mock_write_output_file, mock_get_full_path, mock_parse_test_results, mock_execute_tests, mock_merge_snippet, mock_read_file_for_context, mock_load_roadmap, mock_select_next_task, mock_generate_plan, mock_invoke_coder_llm, test_driver_reporting, tmp_path, caplog):
        """
        Test that autonomous_loop skips ethical analysis if default policy is not loaded.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_reporting['driver']
        mock_code_review_agent = test_driver_reporting['mock_code_review_agent']
        mock_ethical_governance_engine = test_driver_reporting['mock_ethical_governance_engine']

        driver.default_policy_config = None # Explicitly set default_policy_config to None

        mock_code_review_agent.analyze_python.return_value = {'status': 'success', 'static_analysis': [], 'errors': {'flake8': None, 'bandit': None}}

        driver.start_workflow("dummy_roadmap.json", str(tmp_path / "output"), driver.context)

        mock_execute_tests.assert_not_called()
        mock_parse_test_results.assert_not_called()

        mock_code_review_agent.analyze_python.assert_called_once_with(mock_merge_snippet.return_value)
        mock_ethical_governance_engine.enforce_policy.assert_not_called()

        assert "Running code review and security scan for src/feature.py..." in caplog.text
        assert "Default ethical policy not loaded. Skipping ethical analysis." in caplog.text