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
            assert report_data["validation_results"] == mock_validation_results # Should contain the raw results
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
                "tests": {"status": "passed"},
                "code_review": {"status": "error", "errors": {"bandit": "Scan failed"}},
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
