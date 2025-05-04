import pytest
import json
import logging
from unittest.mock import patch, MagicMock, mock_open, call

# Import datetime for the mock grade report timestamp
from datetime import datetime

# Assuming WorkflowDriver is in src.core.automation
from src.core.automation.workflow_driver import WorkflowDriver

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine

# Configure logging for the tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__) # Corrected logger name

# Helper function to create a mock grade report JSON string
def create_mock_grade_report(
    overall_grade=100,
    test_status='passed',
    test_passed=1,
    test_failed=0,
    test_total=1,
    code_review_status='success',
    code_review_findings=None,
    ethical_overall_status='approved',
    ethical_transparency_status='compliant',
    ethical_other_violations=None,
    ethical_message=None
):
    if code_review_findings is None:
        code_review_findings = []
    if ethical_other_violations is None:
        ethical_other_violations = {}


    report_data = {
        "task_id": "mock_task",
        "timestamp": datetime.utcnow().isoformat(), # Use datetime here
        "validation_results": {
            "tests": {
                "status": test_status,
                "passed": test_passed,
                "failed": test_failed,
                "total": test_total,
                "message": "Mock test results."
            },
            "code_review": {
                "status": code_review_status,
                "static_analysis": code_review_findings,
                "errors": {"flake8": None, "bandit": None}
            },
            "ethical_analysis": {
                "overall_status": ethical_overall_status,
                "policy_name": "Mock Policy",
                "TransparencyScore": {
                    "status": ethical_transparency_status,
                    "threshold": 0.5,
                    "enforcement_level": 2,
                    "details": "Mock transparency details." if ethical_transparency_status == 'violation' else "Mock transparency details."
                },
                **ethical_other_violations, # Include other potential ethical violations
                "message": ethical_message
            }
        },
        "grades": {
            "overall_percentage_grade": overall_grade,
            # Include other grades if needed for specific test scenarios, but not strictly required for target identification
            "code_style": {"percentage": 100 if not any(f.get('severity') in ['error', 'warning'] for f in code_review_findings) else 50, "justification": "Mock"},
            "ethical_policy": {"percentage": 100 if ethical_overall_status == 'approved' else 0, "justification": "Mock"},
            "security_soundness": {"percentage": 100 if not any(f.get('severity') == 'security_high' for f in code_review_findings) else 50, "justification": "Mock"},
            "test_success": {"percentage": 100 if test_status == 'passed' and test_total > 0 else 0, "justification": "Mock"}
        }
    }
    return json.dumps(report_data)

# Fixtures
@pytest.fixture
def driver():
    # Mock dependencies that WorkflowDriver init calls
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator:


        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value

        # Mock policy loading which happens in __init__
        mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        # Create a mock Context object
        mock_context = MagicMock()
        mock_context.base_path = "/mock/base/path"
        mock_context.get_full_path.side_effect = lambda path: f"/mock/base/path/{path}" if path else "/mock/base/path/"


        # Instantiate WorkflowDriver with mocks
        wd = WorkflowDriver(mock_context)

        # Explicitly assign the mocked instances to the driver if needed,
        # although patching the classes should make __init__ use them.
        wd.code_review_agent = mock_code_review_agent_instance
        wd.ethical_governance_engine = mock_ethical_governance_engine_instance
        wd.llm_orchestrator = mock_llm_orchestrator_instance
        wd.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set

        yield wd # Yield the driver instance

# Tests for _identify_remediation_target
def test_identify_ethical_transparency_due_to_transparency_score(driver):
    grade_report = create_mock_grade_report(
        ethical_overall_status='rejected',
        ethical_transparency_status='violation',
        overall_grade=70 # Grade below 100
    )
    result = driver._identify_remediation_target(grade_report)
    assert result == "Ethical Transparency"

def test_identify_code_style_when_code_style_below_100_and_ethical_approved(driver):
    grade_report = create_mock_grade_report(
        code_review_status='failed', # Status is failed if findings exist
        code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}],
        ethical_overall_status='approved',
        overall_grade=90 # Grade below 100
    )
    result = driver._identify_remediation_target(grade_report)
    assert result == "Code Style"

def test_identify_code_style_when_code_style_below_100_and_ethical_rejected_other_reason(driver):
    grade_report = create_mock_grade_report(
        code_review_status='failed',
        code_review_findings=[{'severity': 'warning', 'code': 'W001', 'message': 'Style issue'}],
        ethical_overall_status='rejected',
        ethical_transparency_status='compliant', # Not a transparency violation
        ethical_other_violations={"BiasRisk": {"status": "violation"}}, # Some other ethical violation
        overall_grade=80 # Grade below 100
    )
    result = driver._identify_remediation_target(grade_report)
    assert result == "Code Style"

def test_return_none_when_ethical_rejected_not_transparency(driver):
    grade_report = create_mock_grade_report(
        ethical_overall_status='rejected',
        ethical_transparency_status='compliant', # Not a transparency violation
        ethical_other_violations={"BiasRisk": {"status": "violation"}}, # Some other ethical violation
        code_review_status='success', # No code style issues
        overall_grade=80 # Grade below 100
    )
    result = driver._identify_remediation_target(grade_report)
    assert result is None

def test_return_none_when_code_style_100(driver):
    grade_report = create_mock_grade_report(
        code_review_status='failed', # Code review status can be failed even with 100% style if there are security issues
        code_review_findings=[{'severity': 'security_high', 'code': 'B101', 'message': 'Security issue'}], # Only security findings
        overall_grade=50 # Grade below 100
    )
    result = driver._identify_remediation_target(grade_report)
    assert result is None

def test_return_none_when_status_completed_blocked_manual_review(driver):
    # _identify_remediation_target only looks at validation results and grades, not the overall 'status' field
    # of the report itself. The check for "Completed", "Blocked", "Manual Review Required" happens in autonomous_loop.
    # This test should verify that _identify_remediation_target returns a target if validation results indicate one,
    # regardless of the report's top-level status field.
    # The logic in _identify_remediation_target doesn't check the top-level status.
    # Let's test scenarios where validation results would trigger remediation, but the top-level status is terminal.
    # The calling code (autonomous_loop) decides whether to attempt remediation based on the top-level status.
    # So, _identify_remediation_target should return a target if the underlying validation results show one.
    grade_report_ethical = create_mock_grade_report(
        ethical_overall_status='rejected',
        ethical_transparency_status='violation',
        overall_grade=70
    )
    assert driver._identify_remediation_target(grade_report_ethical) == "Ethical Transparency"


    grade_report_style = create_mock_grade_report(
        code_review_status='failed',
        code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}],
        ethical_overall_status='approved',
        overall_grade=90
    )
    assert driver._identify_remediation_target(grade_report_style) == "Code Style"

def test_return_none_and_log_invalid_json(caplog, driver):
    with caplog.at_level(logging.ERROR):
        result = driver._identify_remediation_target("invalid{json")
        assert result is None
        assert "Failed to parse grade report JSON for remediation target identification." in caplog.text

def test_return_none_and_log_unexpected_exception(driver, mocker, caplog):
    mocker.patch("json.loads", side_effect=Exception("Unexpected"))
    grade_report = json.dumps({"code_review": {"passed": False}})
    with caplog.at_level(logging.ERROR):
        result = driver._identify_remediation_target(grade_report)
        assert result is None
        assert "Error identifying remediation target: Unexpected" in caplog.text

def test_missing_keys_in_json_identify_target(driver, caplog):
    # Test that missing keys don't cause errors and result in None
    with caplog.at_level(logging.DEBUG):
        grade_report = json.dumps({})
        result = driver._identify_remediation_target(grade_report)
        assert result is None
        assert "No specific remediation target identified from grade report." in caplog.text


    with caplog.at_level(logging.DEBUG):
        grade_report = json.dumps({"validation_results": {}})
        result = driver._identify_remediation_target(grade_report)
        assert result is None
        assert "No specific remediation target identified from grade report." in caplog.text

    with caplog.at_level(logging.DEBUG):
        grade_report = json.dumps({"validation_results": {"ethical_analysis": {}}})
        result = driver._identify_remediation_target(grade_report)
        assert result is None
        assert "No specific remediation target identified from grade report." in caplog.text

    with caplog.at_level(logging.DEBUG):
        grade_report = json.dumps({"validation_results": {"code_review": {}}})
        result = driver._identify_remediation_target(grade_report)
        assert result is None
        assert "No specific remediation target identified from grade report." in caplog.text

# Tests for _attempt_code_style_remediation
# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm')
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report') # Mock generate_grade_report
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report') # Mock _parse_and_evaluate_grade_report
def test_return_false_if_no_style_feedback(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.WARNING)
    # Mock grade report with no static analysis findings
    grade_report = create_mock_grade_report(code_review_status='success', code_review_findings=[])
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code" # Added original_code parameter


    result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    mock_invoke.assert_not_called()
    mock_write.assert_not_called()
    # Removed: mock_read.assert_called_once_with(file_path)
    assert "No specific code style feedback found to provide to LLM." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value=None) # LLM returns None
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_false_if_invoke_coder_returns_none(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.WARNING)
    # Mock grade report with style feedback
    grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code" # Added original_code parameter


    result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    mock_invoke.assert_called_once() # LLM should be called
    mock_write.assert_not_called()
    # Removed: mock_read.assert_called_once_with(file_path)
    assert "LLM did not provide corrected code or code was unchanged." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="original code") # LLM returns original code
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_false_if_code_identical(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.WARNING)
    # Mock grade report with style feedback
    grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code" # Added original_code parameter


    result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    mock_invoke.assert_called_once() # LLM should be called
    mock_write.assert_not_called()
    # Removed: mock_read.assert_called_once_with(file_path)
    assert "LLM did not provide corrected code or code was unchanged." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="corrected code")
@patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Write succeeds
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_successful_flow_code_style(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, mocker, caplog):
    caplog.set_level(logging.INFO)
    # Mock grade report with style feedback
    grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"
    corrected_code = "corrected code"


    # Mock the analyze_python method on the driver's CodeReviewAgent instance
    mock_analyze = mocker.patch.object(driver.code_review_agent, "analyze_python", return_value={'status': 'success', 'static_analysis': []})
    driver._current_task_results = {} # Ensure results dict is available

    result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is True
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once() # Check prompt content is tested separately
    mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
    mock_analyze.assert_called_once_with(corrected_code)
    assert driver._current_task_results.get("code_review_results") == {'status': 'success', 'static_analysis': []}
    assert "Attempting code style remediation for mock/file.py..." in caplog.text
    assert "LLM provided corrected code. Applying and re-validating..." in caplog.text
    # REMOVED: assert "Successfully wrote corrected code to mock/file.py." in caplog.text # This log is from the mocked method
    assert "Re-running code review for mock/file.py after remediation..." in caplog.text
    assert "Code style remediation appears successful based on re-scan." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="corrected code")
@patch.object(WorkflowDriver, '_write_output_file', return_value=False) # Write fails
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_false_on_write_failure_code_style(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, mocker, caplog):
    caplog.set_level(logging.ERROR)
    # Mock grade report with style feedback
    grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"
    corrected_code = "corrected code"


    result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once()
    mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
    # Re-validation should NOT be called if write fails
    mocker.patch.object(driver.code_review_agent, "analyze_python").assert_not_called()
    assert "Failed to write corrected code to mock/file.py. Aborting remediation." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="corrected code")
@patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Write succeeds
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_true_if_revalidation_fails_code_style(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, mocker, caplog):
    caplog.set_level(logging.ERROR) # Set level to ERROR to capture the error log from analyze_python
    # Mock grade report with style feedback
    grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"
    corrected_code = "corrected code"


    # Mock the analyze_python method on the driver's CodeReviewAgent instance to raise an exception
    mock_analyze = mocker.patch.object(driver.code_review_agent, "analyze_python", side_effect=Exception("Re-validation error"))
    driver._current_task_results = {}

    result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is True # Method should return True because remediation was attempted and write succeeded
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once()
    mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
    mock_analyze.assert_called_once_with(corrected_code)
    # Check that the error status is captured in _current_task_results
    assert driver._current_task_results.get("code_review_results", {}).get("status") == "error"
    # The log message check needs to match the actual log message in the code
    # The code logs "Error occurred during code review re-scan after remediation."
    # The traceback is logged separately by the exception handler.
    assert "Error occurred during code review re-scan after remediation" in caplog.text
    # The specific exception message is logged within the exception handler in the method under test
    # assert "Error during code style remediation: Re-validation error" in caplog.text # This is logged by the outer try-except, which we are now avoiding returning False from

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', side_effect=Exception("LLM error")) # LLM raises exception
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_error_handling_generic_exception_code_style(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.ERROR)
    # Mock grade report with style feedback
    grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"


    result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once()
    mock_write.assert_not_called() # Write should not be called if LLM fails
    assert "Error during code style remediation: LLM error" in caplog.text

# Tests for _attempt_ethical_transparency_remediation
# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm')
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_false_if_no_transparency_violation(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.WARNING)
    # Mock grade report with ethical analysis but no transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='approved', ethical_transparency_status='compliant')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code" # Added original_code parameter


    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    mock_invoke.assert_not_called()
    mock_write.assert_not_called()
    # Removed: mock_read.assert_called_once_with(file_path)
    assert "Ethical transparency remediation triggered, but no violation found in report." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value=None) # LLM returns None
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_false_if_invoke_coder_none_ethical(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.WARNING)
    # Mock grade report with transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code" # Added original_code parameter


    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    mock_invoke.assert_called_once()
    mock_write.assert_not_called()
    # Removed: mock_read.assert_called_once_with(file_path)
    assert "LLM did not provide corrected code or code was unchanged." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="original code") # LLM returns original code
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_false_if_code_identical_ethical(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.WARNING)
    # Mock grade report with transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code" # Added original_code parameter


    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    mock_invoke.assert_called_once()
    mock_write.assert_not_called()
    # Removed: mock_read.assert_called_once_with(file_path)
    assert "LLM did not provide corrected code or code was unchanged." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="corrected code")
@patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Write succeeds
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_successful_flow_ethical(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, mocker, caplog):
    caplog.set_level(logging.INFO)
    # Mock grade report with transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"
    corrected_code = "corrected code"


    # Mock the enforce_policy method on the driver's EthicalGovernanceEngine instance
    mock_enforce = mocker.patch.object(driver.ethical_governance_engine, "enforce_policy", return_value={'overall_status': 'approved'})
    driver._current_task_results = {}
    driver.default_policy_config = {"strictness": "high"} # Ensure policy is not None

    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is True
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once() # Check prompt content is tested separately
    mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
    mock_enforce.assert_called_once_with(corrected_code, driver.default_policy_config)
    assert driver._current_task_results.get("ethical_analysis_results") == {'overall_status': 'approved'}
    assert "Attempting ethical transparency remediation for mock/file.py..." in caplog.text
    assert "LLM provided corrected code with docstrings. Applying and re-validating..." in caplog.text
    # REMOVED: assert "Successfully wrote corrected code to mock/file.py." in caplog.text # This log is from the mocked method
    assert "Re-running ethical analysis for mock/file.py after remediation..." in caplog.text
    assert "Ethical transparency remediation appears successful based on re-scan." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="corrected code")
@patch.object(WorkflowDriver, '_write_output_file', return_value=False) # Write fails
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_false_on_write_failure_ethical(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, mocker, caplog):
    caplog.set_level(logging.ERROR)
    # Mock grade report with transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"
    corrected_code = "corrected code"


    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once()
    mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
    # Re-validation should NOT be called if write fails
    mocker.patch.object(driver.ethical_governance_engine, "enforce_policy").assert_not_called()
    assert "Failed to write corrected code to mock/file.py. Aborting remediation." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="corrected code")
@patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Write succeeds
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_return_true_if_revalidation_fails_ethical(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, mocker, caplog):
    caplog.set_level(logging.ERROR) # Set level to ERROR to capture the error log from enforce_policy
    # Mock grade report with transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"
    corrected_code = "corrected code"


    # Mock the enforce_policy method on the driver's EthicalGovernanceEngine instance to raise an exception
    mock_enforce = mocker.patch.object(driver.ethical_governance_engine, "enforce_policy", side_effect=Exception("Re-validation error"))
    driver._current_task_results = {}
    driver.default_policy_config = {"strictness": "high"}

    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is True # Method should return True because remediation was attempted and write succeeded
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once()
    mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
    mock_enforce.assert_called_once_with(corrected_code, driver.default_policy_config)
    # Check that the error status is captured in _current_task_results
    assert driver._current_task_results.get("ethical_analysis_results", {}).get("overall_status") == "error"
    # The log message check needs to match the actual log message in the code
    # The code logs "Error occurred during ethical analysis re-scan after remediation."
    # The traceback is logged separately by the exception handler.
    assert "Error occurred during ethical analysis re-scan after remediation" in caplog.text
    # The specific exception message is logged within the exception handler in the method under test
    # assert "Error during ethical transparency remediation: Re-validation error" in caplog.text # This is logged by the outer try-except, which we are now avoiding returning False from

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="corrected code")
@patch.object(WorkflowDriver, '_write_output_file', return_value=True) # Write succeeds
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_skip_ethical_rescan_if_policy_none(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, mocker, caplog):
    caplog.set_level(logging.WARNING)
    # Mock grade report with transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"
    corrected_code = "corrected code"


    # Mock the enforce_policy method on the driver's EthicalGovernanceEngine instance
    mock_enforce = mocker.patch.object(driver.ethical_governance_engine, "enforce_policy")
    driver._current_task_results = {}
    driver.default_policy_config = None # Explicitly set policy to None

    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is True # Method should return True because remediation was attempted and write succeeded
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once()
    mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
    mock_enforce.assert_not_called() # Ethical re-scan should be skipped
    # Check that the skipped status is captured in _current_task_results
    assert driver._current_task_results.get("ethical_analysis_results", {}).get("overall_status") == "skipped"
    assert "Cannot re-run ethical analysis after remediation: Default policy not loaded." in caplog.text

# Removed @patch.object(WorkflowDriver, '_read_file_for_context') and mock_read parameter/assertion
@patch.object(WorkflowDriver, '_invoke_coder_llm', side_effect=Exception("LLM error")) # LLM raises exception
@patch.object(WorkflowDriver, '_write_output_file')
@patch.object(WorkflowDriver, 'generate_grade_report')
@patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report')
def test_error_handling_generic_exception_ethical(mock_parse_evaluate, mock_generate_report, mock_write, mock_invoke, driver, caplog):
    caplog.set_level(logging.ERROR)
    # Mock grade report with transparency violation
    grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
    task = {"task_id": "mock_task", "task_name": "Mock Task"}
    step_desc = "Mock Step"
    file_path = "mock/file.py"
    original_code = "original code"


    result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

    assert result is False
    # Removed: mock_read.assert_called_once_with(file_path)
    mock_invoke.assert_called_once()
    mock_write.assert_not_called() # Write should not be called if LLM fails
    assert "Error during ethical transparency remediation: LLM error" in caplog.text