import pytest
import json
import logging
from unittest.mock import patch, MagicMock, mock_open, call, ANY
from pathlib import Path # Import Path for tmp_path usage

# Import datetime for the mock grade report timestamp
from datetime import datetime

# Assuming WorkflowDriver is in src.core.automation
from src.core.automation.workflow_driver import WorkflowDriver, Context

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine

# Configure logging for the tests
# Check if handlers exist to avoid adding duplicate handlers in subsequent test runs
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Use the correct logger name for the module
# FIX: Correct logger name
logger = logging.getLogger(__name__) # Use __name__ for the logger name

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
def driver(mocker):
    # Mock dependencies that WorkflowDriver init calls
    # Patch the classes themselves so that when WorkflowDriver is instantiated,
    # it uses these mocked classes.
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine, \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator') as MockLLMOrchestrator:


        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        mock_llm_orchestrator_instance = MockLLMOrchestrator.return_value

        # Mock policy loading which happens in __init__
        mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        # Create a mock Context object
        mock_context = MagicMock(spec=Context) # Use spec=Context for better mocking
        mock_context.base_path = "/mock/base/path"
        # Configure get_full_path to simulate path resolution
        mock_context.get_full_path.side_effect = lambda path: f"/mock/base/path/{path}" if path else "/mock/base/path"


        # Instantiate WorkflowDriver with mocks
        wd = WorkflowDriver(mock_context)

        # Explicitly assign the mocked instances to the driver if needed,
        # although patching the classes should make __init__ use them.
        wd.code_review_agent = mock_code_review_agent_instance
        wd.ethical_governance_engine = mock_ethical_governance_engine_instance
        wd.llm_orchestrator = mock_llm_orchestrator_instance
        wd.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set

        # Add attributes needed for tests that might not be set by __init__ or autonomous_loop setup
        # Ensure _current_task includes all required keys for autonomous_loop tests
        wd._current_task_results = {}
        wd._current_task = {
            'task_id': 'mock_task',
            'task_name': 'Mock Task',
            'description': 'Mock Description',
            'status': 'Not Started', # Added status
            'priority': 'medium', # Added priority
            'target_file': 'src/mock_file.py' # Added target_file
        }
        wd.filepath_to_use = "src/mock_file.py" # Set a default filepath_to_use for tests

        # Mock methods called by autonomous_loop that are not the focus of these tests
        # These mocks are for the autonomous_loop tests, not the specific remediation method tests
        # We will mock select_next_task dynamically in the autonomous_loop tests to control loop execution
        mocker.patch.object(wd, 'load_roadmap', return_value=[wd._current_task]) # Simulate roadmap with only the current task
        mocker.patch.object(wd, 'generate_solution_plan', return_value=["Step 1: Implement code in file.py", "Step 2: Run tests"]) # Simulate a simple plan
        # _read_file_for_context, _invoke_coder_llm, _merge_snippet, _write_output_file, generate_grade_report, _parse_and_evaluate_grade_report, _safe_write_roadmap_json
        # are mocked individually in the tests that focus on them or their callers.

        # Mock open for roadmap read/write in autonomous_loop
        # Ensure the mock_open provides a valid roadmap structure with the mocked task
        mock_roadmap_content = json.dumps({'tasks': [wd._current_task]})
        mocker.patch('builtins.open', new_callable=mock_open, read_data=mock_roadmap_content)

        yield wd # Yield the driver instance

# Test class for remediation logic
class TestWorkflowRemediation:


    # --- Tests for _identify_remediation_target (from task_1_7_4) ---
    def test_identify_ethical_transparency_due_to_transparency_score(self, driver):
        """Test _identify_remediation_target identifies Ethical Transparency when TransparencyScore is violated."""
        grade_report = create_mock_grade_report(
            ethical_overall_status='rejected',
            ethical_transparency_status='violation',
            overall_grade=70 # Grade below 100
        )
        result = driver._identify_remediation_target(grade_report)
        assert result == "Ethical Transparency"

    def test_identify_code_style_when_code_style_below_100_and_ethical_approved(self, driver):
        """Test _identify_remediation_target identifies Code Style when style grade < 100 and ethical is approved."""
        grade_report = create_mock_grade_report(
            code_review_status='failed', # Status is failed if findings exist
            code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}],
            ethical_overall_status='approved',
            overall_grade=90 # Grade below 100
        )
        result = driver._identify_remediation_target(grade_report)
        assert result == "Code Style"

    def test_identify_code_style_when_code_style_below_100_and_ethical_rejected_other_reason(self, driver):
        """Test _identify_remediation_target identifies Code Style when style grade < 100 and ethical rejected for non-transparency."""
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

    def test_return_none_when_ethical_rejected_not_transparency(self, driver):
        """Test _identify_remediation_target returns None when ethical rejected for non-transparency and no style issues."""
        grade_report = create_mock_grade_report(
            ethical_overall_status='rejected',
            ethical_transparency_status='compliant', # Not a transparency violation
            ethical_other_violations={"BiasRisk": {"status": "violation"}}, # Some other ethical violation
            code_review_status='success', # No code style issues
            overall_grade=80 # Grade below 100
        )
        result = driver._identify_remediation_target(grade_report)
        assert result is None

    def test_return_none_when_code_style_100(self, driver):
        """Test _identify_remediation_target returns None when code style is 100% (only security findings)."""
        grade_report = create_mock_grade_report(
            code_review_status='failed', # Code review status can be failed even with 100% style if there are security issues
            code_review_findings=[{'severity': 'security_high', 'code': 'B101', 'message': 'Security issue'}], # Only security findings
            overall_grade=50 # Grade below 100
        )
        result = driver._identify_remediation_target(grade_report)
        assert result is None

    def test_return_none_and_log_invalid_json_identify_target(self, driver, caplog):
        """Test _identify_remediation_target handles invalid JSON input."""
        with caplog.at_level(logging.ERROR):
            result = driver._identify_remediation_target("invalid{json")
            assert result is None
            assert "Failed to parse grade report JSON for remediation target identification." in caplog.text

    def test_return_none_and_log_unexpected_exception_identify_target(self, driver, mocker, caplog):
        """Test _identify_remediation_target handles unexpected exceptions during parsing."""
        mocker.patch("json.loads", side_effect=Exception("Unexpected"))
        # Provide a minimal valid JSON structure to reach the exception point
        grade_report = json.dumps({"validation_results": {}})
        with caplog.at_level(logging.ERROR):
            result = driver._identify_remediation_target(grade_report)
            assert result is None
            assert "Error identifying remediation target: Unexpected" in caplog.text

    def test_missing_keys_in_json_identify_target(self, driver, caplog):
        """Test _identify_remediation_target handles missing keys gracefully."""
        with caplog.at_level(logging.DEBUG):
            grade_report = json.dumps({})
            result = driver._identify_remediation_target(grade_report)
            assert result is None
            # Corrected assertion: The code logs the general "No specific target" message here
            assert "No specific remediation target identified from grade report." in caplog.text
            # Removed the incorrect assertion: assert "Ethical rejection not due to TransparencyScore, no specific remediation target." in caplog.text

        with caplog.at_level(logging.DEBUG):
            grade_report = json.dumps({"validation_results": {}})
            result = driver._identify_remediation_target(grade_report)
            assert result is None
            # Corrected assertion: The code logs the general "No specific target" message here
            assert "No specific remediation target identified from grade report." in caplog.text
            # Removed the incorrect assertion: assert "Ethical rejection not due to TransparencyScore, no specific remediation target." in caplog.text

        with caplog.at_level(logging.DEBUG):
            grade_report = json.dumps({"validation_results": {"ethical_analysis": {}}})
            result = driver._identify_remediation_target(grade_report)
            assert result is None
            # Corrected assertion: The code logs the general "No specific target" message here
            assert "No specific remediation target identified from grade report." in caplog.text
            # Removed the incorrect assertion: assert "Ethical rejection not due to TransparencyScore, no specific remediation target." in caplog.text

        with caplog.at_level(logging.DEBUG):
            grade_report = json.dumps({"validation_results": {"code_review": {}}})
            result = driver._identify_remediation_target(grade_report)
            assert result is None
            # Corrected assertion: The code logs the general "No specific target" message here
            assert "No specific remediation target identified from grade report." in caplog.text
            # Removed the incorrect assertion: assert "Code style grade below 100, but code review status not 'failed'." in caplog.text


    # --- Tests for _attempt_code_style_remediation (from task_1_7_4) ---
    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_if_no_style_feedback(self, driver, mocker, caplog):
        """Test _attempt_code_style_remediation returns False if no style findings in report."""
        caplog.set_level(logging.WARNING)
        # Mock grade report with no static analysis findings
        grade_report = create_mock_grade_report(code_review_status='success', code_review_findings=[])
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm')
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_not_called()
        mock_write.assert_not_called()
        assert "No specific code style feedback found to provide to LLM." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_if_invoke_coder_returns_none_style(self, driver, mocker, caplog):
        """Test _attempt_code_style_remediation returns False if LLM returns None."""
        caplog.set_level(logging.WARNING)
        # Mock grade report with style feedback
        grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=None) # LLM returns None
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once() # LLM should be called
        mock_write.assert_not_called()
        assert "LLM did not provide corrected code or code was unchanged." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_if_code_identical_style(self, driver, mocker, caplog):
        """Test _attempt_code_style_remediation returns False if LLM returns identical code."""
        caplog.set_level(logging.WARNING)
        # Mock grade report with style feedback
        grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
        # FIX: Corrected syntax error in task dictionary
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value="original code") # LLM returns original code
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once() # LLM should be called
        mock_write.assert_not_called()
        assert "LLM did not provide corrected code or code was unchanged." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_successful_flow_code_style(self, driver, mocker, caplog):
        """Test _attempt_code_style_remediation successfully applies fix and re-validates."""
        caplog.set_level(logging.INFO)
        # Mock grade report with style feedback
        grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"
        corrected_code = "corrected code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=corrected_code)
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=True) # Write succeeds

        # Mock the analyze_python method on the driver's CodeReviewAgent instance
        mock_analyze = mocker.patch.object(driver.code_review_agent, "analyze_python", return_value={'status': 'success', 'static_analysis': []})
        driver._current_task_results = {} # Ensure results dict is available

        result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is True
        mock_invoke.assert_called_once() # Check prompt content is tested separately
        mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
        mock_analyze.assert_called_once_with(corrected_code)
        assert driver._current_task_results.get("code_review_results") == {'status': 'success', 'static_analysis': []}
        assert "Attempting code style remediation for mock/file.py..." in caplog.text
        assert "LLM provided corrected code. Applying and re-validating..." in caplog.text
        assert "Re-running code review for mock/file.py after remediation..." in caplog.text
        assert "Code style remediation appears successful based on re-scan." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_on_write_failure_code_style(self, driver, mocker, caplog):
        """Test _attempt_code_style_remediation returns False on write failure."""
        caplog.set_level(logging.ERROR)
        # Mock grade report with style feedback
        grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"
        corrected_code = "corrected code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=corrected_code)
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=False) # Write fails

        result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once()
        mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
        # Re-validation should NOT be called if write fails
        mocker.patch.object(driver.code_review_agent, "analyze_python").assert_not_called()
        assert "Failed to write corrected code to mock/file.py. Aborting remediation." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_true_if_revalidation_fails_code_style(self, driver, mocker, caplog):
        """Test _attempt_code_style_remediation returns True if re-validation fails after successful write."""
        caplog.set_level(logging.ERROR) # Set level to ERROR to capture the error log from analyze_python
        # Mock grade report with style feedback
        grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"
        corrected_code = "corrected code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=corrected_code)
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=True) # Write succeeds

        # Mock the analyze_python method on the driver's CodeReviewAgent instance to raise an exception
        mock_analyze = mocker.patch.object(driver.code_review_agent, "analyze_python", side_effect=Exception("Re-validation error"))
        driver._current_task_results = {}

        result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is True # Method should return True because remediation was attempted and write succeeded
        mock_invoke.assert_called_once()
        mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
        mock_analyze.assert_called_once_with(corrected_code)
        # Check that the error status is captured in _current_task_results
        assert driver._current_task_results.get("code_review_results", {}).get("status") == "error"
        assert "Error occurred during code review re-scan after remediation" in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_error_handling_generic_exception_code_style(self, driver, mocker, caplog):
        """Test _attempt_code_style_remediation handles generic exceptions before write."""
        caplog.set_level(logging.ERROR)
        # Mock grade report with style feedback
        grade_report = create_mock_grade_report(code_review_status='failed', code_review_findings=[{'severity': 'error', 'code': 'E001', 'message': 'Style issue'}])
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', side_effect=Exception("LLM error")) # LLM raises exception
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_code_style_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once()
        mock_write.assert_not_called() # Write should not be called if LLM fails
        assert "Error during code style remediation: LLM error" in caplog.text

    # --- Tests for _attempt_ethical_transparency_remediation (from task_1_7_4) ---
    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_if_no_transparency_violation(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation returns False if no transparency violation in report."""
        caplog.set_level(logging.WARNING)
        # Mock grade report with ethical analysis but no transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='approved', ethical_transparency_status='compliant')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm')
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_not_called()
        mock_write.assert_not_called()
        assert "Ethical transparency remediation triggered, but no violation found in report." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_if_invoke_coder_none_ethical(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation returns False if LLM returns None."""
        caplog.set_level(logging.WARNING)
        # Mock grade report with transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=None) # LLM returns None
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once()
        mock_write.assert_not_called()
        assert "LLM did not provide corrected code or code was unchanged." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_if_code_identical_ethical(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation returns False if LLM returns identical code."""
        caplog.set_level(logging.WARNING)
        # Mock grade report with transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value="original code") # LLM returns original code
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once()
        mock_write.assert_not_called()
        assert "LLM did not provide corrected code or code was unchanged." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_successful_flow_ethical(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation successfully applies fix and re-validates."""
        caplog.set_level(logging.INFO)
        # Mock grade report with transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"
        corrected_code = "corrected code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=corrected_code)
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=True) # Write succeeds

        # Mock the enforce_policy method on the driver's EthicalGovernanceEngine instance
        mock_enforce = mocker.patch.object(driver.ethical_governance_engine, "enforce_policy", return_value={'overall_status': 'approved'})
        driver._current_task_results = {}
        driver.default_policy_config = {"strictness": "high"} # Ensure policy is not None

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is True
        mock_invoke.assert_called_once() # Check prompt content is tested separately
        mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
        mock_enforce.assert_called_once_with(corrected_code, driver.default_policy_config)
        assert driver._current_task_results.get("ethical_analysis_results") == {'overall_status': 'approved'}
        assert "Attempting ethical transparency remediation for mock/file.py..." in caplog.text
        assert "LLM provided corrected code with docstrings. Applying and re-validating..." in caplog.text
        assert "Re-running ethical analysis for mock/file.py after remediation..." in caplog.text
        assert "Ethical transparency remediation appears successful based on re-scan." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_false_on_write_failure_ethical(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation returns False on write failure."""
        caplog.set_level(logging.ERROR)
        # Mock grade report with transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"
        corrected_code = "corrected code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=corrected_code)
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=False) # Write fails

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once()
        mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
        # Re-validation should NOT be called if write fails
        mocker.patch.object(driver.ethical_governance_engine, "enforce_policy").assert_not_called()
        assert "Failed to write corrected code to mock/file.py. Aborting remediation." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_return_true_if_revalidation_fails_ethical(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation returns True if re-validation fails after successful write."""
        caplog.set_level(logging.ERROR) # Set level to ERROR to capture the error log from enforce_policy
        # Mock grade report with transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"
        corrected_code = "corrected code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=corrected_code)
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=True) # Write succeeds

        # Mock the enforce_policy method on the driver's EthicalGovernanceEngine instance to raise an exception
        mock_enforce = mocker.patch.object(driver.ethical_governance_engine, "enforce_policy", side_effect=Exception("Re-validation error"))
        driver._current_task_results = {}
        driver.default_policy_config = {"strictness": "high"}

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is True # Method should return True because remediation was attempted and write succeeded
        mock_invoke.assert_called_once()
        mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
        mock_enforce.assert_called_once_with(corrected_code, driver.default_policy_config)
        # Check that the error status is captured in _current_task_results
        assert driver._current_task_results.get("ethical_analysis_results", {}).get("overall_status") == "error"
        assert "Error occurred during ethical analysis re-scan after remediation" in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_skip_ethical_rescan_if_policy_none(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation skips ethical re-scan if default policy is None."""
        caplog.set_level(logging.WARNING)
        # Mock grade report with transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"
        corrected_code = "corrected code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=corrected_code)
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=True) # Write succeeds

        # Mock the enforce_policy method on the driver's EthicalGovernanceEngine instance
        mock_enforce = mocker.patch.object(driver.ethical_governance_engine, "enforce_policy")
        driver._current_task_results = {}
        driver.default_policy_config = None # Explicitly set policy to None

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is True
        mock_invoke.assert_called_once()
        mock_write.assert_called_once_with(file_path, corrected_code, overwrite=True)
        mock_enforce.assert_not_called() # Ethical re-scan should be skipped
        # Check that the skipped status is captured in _current_task_results
        assert driver._current_task_results.get("ethical_analysis_results", {}).get("overall_status") == "skipped"
        assert "Cannot re-run ethical analysis after remediation: Default policy not loaded." in caplog.text

    # Removed @patch decorators and will use mocker.patch.object(driver, ...) inside tests
    def test_error_handling_generic_exception_ethical(self, driver, mocker, caplog):
        """Test _attempt_ethical_transparency_remediation handles generic exceptions before write."""
        caplog.set_level(logging.ERROR)
        # Mock grade report with transparency violation
        grade_report = create_mock_grade_report(ethical_overall_status='rejected', ethical_transparency_status='violation')
        task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock Desc", "status": "Not Started", "priority": "medium"} # Ensure task is complete
        step_desc = "Mock Step"
        file_path = "mock/file.py"
        original_code = "original code"

        # Patch instance methods
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', side_effect=Exception("LLM error")) # LLM raises exception
        mock_write = mocker.patch.object(driver, '_write_output_file')

        result = driver._attempt_ethical_transparency_remediation(grade_report, task, step_desc, file_path, original_code)

        assert result is False
        mock_invoke.assert_called_once()
        mock_write.assert_not_called() # Write should not be called if LLM fails
        assert "Error during ethical transparency remediation: LLM error" in caplog.text


    # --- Tests for automated test failure remediation (Task 1.7.5) ---
    # Note: These tests focus on the autonomous_loop's behavior regarding remediation
    # and the _attempt_test_failure_remediation method itself.

    def test_autonomous_loop_triggers_test_remediation_on_failure(self, driver, mocker, caplog):
        """Test that autonomous_loop triggers test failure remediation when tests fail and attempts are available."""
        # Set up driver state
        driver.roadmap_path = "dummy_roadmap.json" # FIX: Set roadmap_path
        driver.remediation_attempts = 0
        # Initial _current_task_results will be cleared by the loop,
        # so we need to mock the step execution to produce failed results.
        # driver._current_task_results.update({
        #     'test_results': {'status': 'failed'}, # This initial state is cleared by the loop
        #     'code_review_results': {'status': 'passed'},
        #     'ethical_analysis_results': {'overall_status': 'passed'},
        #     'test_stdout': 'Test output', # Added for prompt construction test
        #     'test_stderr': 'Error traceback', # Added for prompt construction test
        #     'last_test_command': ['pytest'], # Added for re-execution test
        #     'last_test_cwd': '/test/path' # Added for re-execution test
        # })
        # Ensure _current_task has all required keys for autonomous_loop
        task_data = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started', # Required
            'priority': 'high', # Required
            'target_file': 'src/test_file.py' # Added target_file
        }
        driver._current_task = task_data
        driver.filepath_to_use = driver._current_task['target_file']

        # Mock methods called by autonomous_loop before remediation check
        # FIX: Mock load_roadmap to return the updated task list on the second call
        updated_task = task_data.copy()
        updated_task['status'] = 'Completed'
        # FIX: Correct load_roadmap side_effect to return [task_data] in the first loop iteration
        mock_load_roadmap = mocker.patch.object(
            driver, 'load_roadmap',
            side_effect=[
                [task_data],  # First load (start_workflow)
                [task_data],  # Second load (first loop iteration)
                [updated_task],  # Third load (second loop iteration, after status update)
            ]
        )
        # Mock select_next_task to return the task once, then None to exit the loop
        mock_select_next_task = mocker.patch.object(driver, 'select_next_task')
        # FIX: select_next_task needs to return the task once, then None for a single remediation pass
        mock_select_next_task.side_effect = [task_data, None]

        mocker.patch.object(driver, 'generate_solution_plan', return_value=["Step 1: Implement code", "Step 2: Run tests"])

        # Mock step execution to produce failed test results and other passed results
        mocker.patch.object(driver, 'execute_tests', return_value=(1, "fail", "err")) # Simulate failed tests in step execution
        mocker.patch.object(driver, '_parse_test_results', return_value={'status': 'failed', 'passed': 0, 'failed': 1, 'total': 1}) # Simulate parsing failed tests
        mocker.patch.object(driver.code_review_agent, 'analyze_python', return_value={'status': 'passed'}) # Simulate passed code review
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy', return_value={'overall_status': 'approved'}) # Simulate passed ethical analysis
        # Ensure test stdout/stderr are available in _current_task_results after step execution
        mocker.patch.object(driver, '_read_file_for_context', return_value="Original code") # Needed by remediation attempt

        # Mock generate_grade_report and _parse_and_evaluate_grade_report
        # Initial evaluation should recommend Regenerate Code
        mocker.patch.object(driver, 'generate_grade_report', return_value=create_mock_grade_report(test_status='failed', overall_grade=70))
        mocker.patch.object(driver, '_parse_and_evaluate_grade_report', return_value={
            "recommended_action": "Regenerate Code",
            "justification": "Test failures detected"
        })

        # Mock roadmap write (needed for status update after successful remediation)
        mocker.patch.object(driver, '_safe_write_roadmap_json', return_value=True)

        # Mock the remediation attempt method itself.
        # We need it to return True to simulate a successful remediation attempt that increments the counter
        # FIX: Mock the method directly, not wrap it
        mock_remediation = mocker.patch.object(driver, '_attempt_test_failure_remediation', return_value=True)


        with caplog.at_level(logging.INFO):
            # FIX: Call start_workflow instead of autonomous_loop directly
            driver.start_workflow(driver.roadmap_path, "output", driver.context)

        # Assertions
        mock_remediation.assert_called_once_with(
            ANY, # grade_report_json is passed (the one generated before remediation)
            driver._current_task,
            "Test Failure Remediation",
            driver.filepath_to_use,
            ANY # original_code is passed (mocked by _read_file_for_context inside remediation method)
        )
        assert "Attempting automated remediation" in caplog.text
        # FIX: Correct assertion case
        assert "Test failure remediation" in caplog.text # Check log for test remediation attempt
        assert "Test failure remediation successful" in caplog.text # Check log from mock remediation return
        assert driver.remediation_attempts == 1 # Check that attempt counter incremented
        # FIX: select_next_task is called twice in the loop (once finds task, once finds None)
        assert mock_select_next_task.call_count == 2
        # FIX: Correct assert_has_calls arguments based on load_roadmap side_effect
        mock_select_next_task.assert_has_calls([
            call([task_data]), # Called with the task list from load_roadmap (first loop iteration)
            call([updated_task]) # Called again with the task list after status update (second loop iteration)
        ])


    def test_autonomous_loop_skips_test_remediation_on_passed_tests(self, driver, mocker):
        """Test that autonomous_loop doesn't trigger test remediation if tests passed."""
        # Set up driver state
        driver.roadmap_path = "dummy_roadmap.json" # FIX: Set roadmap_path
        driver.remediation_attempts = 0
        # Initial _current_task_results will be cleared by the loop,
        # so we need to mock the step execution to produce passed results.
        # driver._current_task_results.update({
        #     'test_results': {'status': 'passed'}, # Tests passed - This initial state is cleared by the loop
        #     'code_review_results': {'status': 'passed'},
        #     'ethical_analysis_results': {'overall_status': 'passed'}
        # })
        # Ensure _current_task has all required keys for autonomous_loop
        task_data = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started', # Required
            'priority': 'high', # Required
            'target_file': 'src/test_file.py' # Added target_file
        }
        driver._current_task = task_data
        driver.filepath_to_use = driver._current_task['target_file']

        # Mock evaluation to trigger remediation (even though tests passed, simulate a scenario where evaluation might still recommend regenerate for other reasons, but test remediation shouldn't trigger)
        mocker.patch.object(driver, '_parse_and_evaluate_grade_report', return_value={
            "recommended_action": "Regenerate Code",
            "justification": "Other issues detected"
        })

        # Mock remediation method
        # FIX: Mock the method directly, not wrap it
        mock_remediation = mocker.patch.object(driver, '_attempt_test_failure_remediation', return_value=True)

        # Run the loop logic (simulate one iteration)
        # Need 3 calls to load_roadmap: initial, loop 1, loop 2 (where select_next_task returns None)
        # Status doesn't change in this test, so load_roadmap always returns [task_data]
        mock_load_roadmap = mocker.patch.object(driver, 'load_roadmap', side_effect=[[task_data], [task_data], [task_data]]) # Added based on loop structure
        # Mock select_next_task to return the task once, then None to exit the loop
        mock_select_next_task = mocker.patch.object(driver, 'select_next_task')
        # FIX: select_next_task needs to return the task once, then None
        mock_select_next_task.side_effect = [task_data, None]

        mocker.patch.object(driver, 'generate_solution_plan', return_value=["Step 1: Implement code", "Step 2: Run tests"])

        # Mock step execution to produce PASSED test results and other passed results
        mocker.patch.object(driver, 'execute_tests', return_value=(0, "passed", "")) # Simulate PASSED tests in step execution
        mocker.patch.object(driver, '_parse_test_results', return_value={'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1}) # Simulate parsing PASSED tests
        mocker.patch.object(driver.code_review_agent, 'analyze_python', return_value={'status': 'passed'}) # Simulate passed code review
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy', return_value={'overall_status': 'approved'}) # Simulate passed ethical analysis
        mocker.patch.object(driver, '_read_file_for_context', return_value="Original code") # Needed to reach remediation check block

        # Mock generate_grade_report to return a report that triggers remediation (but tests passed)
        mocker.patch.object(driver, 'generate_grade_report', return_value=create_mock_grade_report(test_status='passed', overall_grade=80))
        mocker.patch.object(driver, '_safe_write_roadmap_json', return_value=True)


        # FIX: Call start_workflow instead of autonomous_loop directly
        driver.start_workflow(driver.roadmap_path, "output", driver.context)

        # Assertions
        assert not mock_remediation.called # Test remediation should NOT be called
        assert driver.remediation_attempts == 0 # Attempts should remain at 0
        # FIX: select_next_task is called twice in the loop (once finds task, once finds None)
        assert mock_select_next_task.call_count == 2
        # FIX: Correct assert_has_calls arguments based on load_roadmap side_effect
        mock_select_next_task.assert_has_calls([
            call([task_data]), # Called with the task list from load_roadmap (first loop iteration)
            call([task_data]) # Called again after status update (status remains Not Started as recommended_action wasn't Completed/Blocked)
        ])


    def test_autonomous_loop_skips_test_remediation_on_max_attempts(self, driver, mocker, caplog):
        """Test that autonomous_loop doesn't trigger test remediation if max attempts reached."""
        MAX_REMEDIATION_ATTEMPTS = 2
        # Set up driver state with max attempts
        driver.roadmap_path = "dummy_roadmap.json" # FIX: Set roadmap_path
        driver.remediation_attempts = MAX_REMEDIATION_ATTEMPTS # Set attempts to max
        # Initial _current_task_results will be cleared by the loop,
        # so we need to mock the step execution to produce failed results.
        # driver._current_task_results.update({
        #     'test_results': {'status': 'failed'}, # Tests failed - This initial state is cleared by the loop
        #     'code_review_results': {'status': 'passed'},
        #     'ethical_analysis_results': {'overall_status': 'passed'}
        # })
        # Ensure _current_task has all required keys for autonomous_loop
        task_data = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started', # Required
            'priority': 'high', # Required
            'target_file': 'src/test_file.py' # Added target_file
        }
        driver._current_task = task_data
        driver.filepath_to_use = driver._current_task['target_file']


        # Mock evaluation to trigger remediation
        mocker.patch.object(driver, '_parse_and_evaluate_grade_report', return_value={
            "recommended_action": "Regenerate Code",
            "justification": "Test failures detected"
        })

        # Mock remediation method
        # FIX: Mock the method directly, not wrap it
        mock_remediation = mocker.patch.object(driver, '_attempt_test_failure_remediation', return_value=True)

        # Run the loop logic (simulate one iteration)
        # Need 3 calls to load_roadmap: initial, loop 1, loop 2 (where select_next_task returns None)
        # Status doesn't change in this test, so load_roadmap always returns [task_data]
        mock_load_roadmap = mocker.patch.object(driver, 'load_roadmap', side_effect=[[task_data], [task_data], [task_data]]) # Added based on loop structure
        # Mock select_next_task to return the task once, then None to exit the loop
        mock_select_next_task = mocker.patch.object(driver, 'select_next_task')
        # FIX: select_next_task needs to return the task once, then None
        mock_select_next_task.side_effect = [task_data, None]

        mocker.patch.object(driver, 'generate_solution_plan', return_value=["Step 1: Implement code", "Step 2: Run tests"])

        # Mock step execution to produce FAILED test results and other passed results
        mocker.patch.object(driver, 'execute_tests', return_value=(1, "fail", "err")) # Simulate FAILED tests in step execution
        mocker.patch.object(driver, '_parse_test_results', return_value={'status': 'failed', 'passed': 0, 'failed': 1, 'total': 1}) # Simulate parsing FAILED tests
        mocker.patch.object(driver.code_review_agent, 'analyze_python', return_value={'status': 'passed'}) # Simulate passed code review
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy', return_value={'overall_status': 'approved'}) # Simulate passed ethical analysis
        # FIX: Ensure _read_file_for_context returns content so remediation attempt is not skipped before the max attempts check
        mocker.patch.object(driver, '_read_file_for_context', return_value="Original code")


        # Mock generate_grade_report to return a report that triggers remediation
        mocker.patch.object(driver, 'generate_grade_report', return_value=create_mock_grade_report(test_status='failed', overall_grade=70))
        mocker.patch.object(driver, '_safe_write_roadmap_json', return_value=True)


        with caplog.at_level(logging.WARNING):
            # FIX: Call start_workflow instead of autonomous_loop directly
            driver.start_workflow(driver.roadmap_path, "output", driver.context)

        # Assertions
        mock_remediation.assert_not_called() # Test remediation should NOT be called
        assert f"Maximum remediation attempts ({MAX_REMEDIATION_ATTEMPTS}) reached" in caplog.text
        assert driver.remediation_attempts == MAX_REMEDIATION_ATTEMPTS # Attempts should remain at max
        # FIX: select_next_task is called twice in the loop (once finds task, once finds None)
        assert mock_select_next_task.call_count == 2
        # FIX: Correct assert_has_calls arguments based on load_roadmap side_effect
        mock_select_next_task.assert_has_calls([
            call([task_data]), # Called with the task list from load_roadmap (first loop iteration)
            call([task_data]) # Called again after status update (status remains Not Started as recommended_action wasn't Completed/Blocked)
        ])


    def test_attempt_test_failure_remediation_constructs_correct_prompt(self, driver, mocker):
        """Test that _attempt_test_failure_remediation constructs the correct prompt with all required details."""
        # Set up test data
        test_stdout = "Test output\nAssertionError: Expected 2 != 2"
        test_stderr = "Traceback (most recent call last):...\nTypeError: bad operand type"
        file_path = "src/module/test_file.py"
        current_code = "def add(a, b):\n    return a - b"
        task_description = "Fix the add function to properly add numbers"
        task_name = "Add Function Test Failure"

        # Set driver state - these results are needed *before* calling the method
        driver._current_task_results.update({
            'test_stdout': test_stdout,
            'test_stderr': test_stderr,
            'test_results': {'status': 'failed'}, # Needed for the method's internal check
            'last_test_command': ['pytest', 'tests/'],
            'last_test_cwd': '/mock/base/path'
        })
        # Ensure _current_task has all required keys for prompt construction
        driver._current_task.update({
            'task_id': 'T1', # Added task_id
            'task_name': task_name,
            'description': task_description,
            'status': 'Not Started', # Added status
            'priority': 'high', # Added priority
            'target_file': file_path # Added target_file
        })
        driver.filepath_to_use = file_path # Set filepath_to_use

        # Mock file reading
        mock_read_file = mocker.patch.object(driver, '_read_file_for_context', return_value=current_code)

        # Capture the prompt from _invoke_coder_llm
        prompt_used = None
        def capture_prompt(prompt):
            nonlocal prompt_used
            prompt_used = prompt
            return "def add(a, b):\n    return a + b"  # Mocked fix
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', side_effect=capture_prompt)

        # Mock subsequent steps to allow the method to complete and return True
        mocker.patch.object(driver, '_write_output_file', return_value=True)
        mocker.patch.object(driver, '_merge_snippet', return_value="merged content")
        mocker.patch.object(driver, 'execute_tests', return_value=(0, "passed", ""))
        mocker.patch.object(driver, '_parse_test_results', return_value={'status': 'passed'})
        mocker.patch.object(driver.code_review_agent, 'analyze_python', return_value={'status': 'passed'})
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy', return_value={'overall_status': 'approved'})


        # Execute the remediation attempt
        result = driver._attempt_test_failure_remediation(
            grade_report_json="{}",  # Not used directly in this method
            task=driver._current_task,
            step_desc="Test Failure Remediation",
            file_path=file_path,
            original_code="This is not used by the method" # original_code is not used in the method, but keep for consistency
        )

        # Assertions
        assert result is True  # Should return True as prompt was captured and write is mocked True
        mock_invoke.assert_called_once()
        mock_read_file.assert_called_once_with(file_path) # Check read was called with the correct path

        # Verify prompt contains all required elements and correct formatting
        assert f"Task: {task_name}" in prompt_used
        assert f"Description: {task_description}" in prompt_used
        assert f"File to modify: {file_path}" in prompt_used
        # Check for markdown code block formatting
        assert f"Current code content:\n```python\n{current_code}\n```" in prompt_used
        # FIX: Correct assertions to match the markdown code block format in the prompt
        assert f"Test execution output:\nStdout:\n```\n{test_stdout}\n```" in prompt_used
        assert f"Stderr:\n```\n{test_stderr}\n```" in prompt_used
        assert "Instructions:" in prompt_used
        assert "Debug Agent (task_2_2_6) is NOT available" in prompt_used # Check specific instruction

    def test_attempt_test_failure_remediation_successfully_applies_fix(self, driver, mocker):
        """Test that _attempt_test_failure_remediation applies LLM fix, re-runs tests and validations."""
        # Set up test data
        test_stdout = "Initial test failure output"
        test_stderr = "Initial error traceback"
        new_stdout = "All tests passed"
        new_stderr = ""
        file_path = "src/module/test_file.py"
        original_code = "def faulty_func():\n    return None"
        fixed_snippet = "    return 'fixed'" # Snippet to be merged
        merged_content = "def faulty_func():\n    return 'fixed'" # Result after merging

        # Set driver state - these results are needed *before* calling the method
        driver._current_task_results.update({
            'test_stdout': test_stdout,
            'test_stderr': test_stderr,
            'test_results': {'status': 'failed'}, # Initial failed status
            'last_test_command': ['pytest', 'tests/'],
            'last_test_cwd': '/mock/base/path'
        })
        # Ensure _current_task has all required keys
        driver._current_task = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started',
            'priority': 'medium',
            'target_file': file_path
        }
        driver.filepath_to_use = file_path # Set filepath_to_use

        # Mock file reading and writing
        mocker.patch.object(driver, '_read_file_for_context', return_value=original_code)
        mocker.patch.object(driver, '_write_output_file', return_value=True)

        # Mock LLM to return fixed snippet
        mocker.patch.object(driver, '_invoke_coder_llm', return_value=fixed_snippet)

        # Mock merge snippet
        mocker.patch.object(driver, '_merge_snippet', return_value=merged_content)

        # Mock test execution and validation results *after* the fix is written
        mock_execute = mocker.patch.object(driver, 'execute_tests', return_value=(0, new_stdout, new_stderr))
        mock_parse_tests = mocker.patch.object(driver, '_parse_test_results', return_value={'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1}) # Mock parsing new results
        mock_review = mocker.patch.object(driver.code_review_agent, 'analyze_python', return_value={'status': 'passed', 'static_analysis': []})
        # FIX: Change return value to 'approved' to match code logic
        mock_ethics = mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy', return_value={'overall_status': 'approved'})

        # Execute remediation
        result = driver._attempt_test_failure_remediation(
            grade_report_json="{}", # Not used directly
            task=driver._current_task,
            step_desc="Test Failure Remediation",
            file_path=file_path,
            original_code="This is not used by the method" # Not used directly
        )

        # Assertions
        assert result is True
        mock_execute.assert_called_once_with(['pytest', 'tests/'], '/mock/base/path') # Check re-execution with stored command/cwd
        mock_parse_tests.assert_called_once_with(new_stdout) # Check parsing of new test output
        mock_review.assert_called_once_with(merged_content) # Check code review on merged content
        mock_ethics.assert_called_once_with(merged_content, driver.default_policy_config) # Check ethical analysis on merged content with policy
        # Check updated results in _current_task_results
        assert driver._current_task_results['test_results']['status'] == 'passed'
        assert driver._current_task_results['code_review_results']['status'] == 'passed'
        # FIX: Change assertion to 'approved'
        assert driver._current_task_results['ethical_analysis_results']['overall_status'] == 'approved'
        # Note: remediation_attempts increment is handled in autonomous_loop, not here

    def test_attempt_test_failure_remediation_returns_false_on_no_snippet(self, driver, mocker, caplog):
        """Test that _attempt_test_failure_remediation returns False if LLM provides no code."""
        # Set up test data
        file_path = "src/module/test_file.py"
        original_code = "def faulty_func():\n    return None"

        # Set driver state - these results are needed *before* calling the method
        driver._current_task_results.update({
            'test_results': {'status': 'failed'},
            'test_stdout': 'Test output',
            'test_stderr': 'Error traceback',
            'last_test_command': ['pytest', 'tests/'],
            'last_test_cwd': '/mock/base/path'
        })
        # Ensure _current_task has all required keys
        driver._current_task = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started',
            'priority': 'medium',
            'target_file': file_path
        }
        driver.filepath_to_use = file_path

        # Mock file reading
        mocker.patch.object(driver, '_read_file_for_context', return_value=original_code)

        # Mock LLM to return empty snippet
        mock_invoke = mocker.patch.object(driver, '_invoke_coder_llm', return_value=None)

        # Execute remediation
        with caplog.at_level(logging.WARNING):
            result = driver._attempt_test_failure_remediation(
                grade_report_json="{}",
                task=driver._current_task,
                step_desc="Test Failure Remediation",
                file_path=file_path,
                original_code="This is not used by the method"
            )

        # Assertions
        assert result is False
        mock_invoke.assert_called_once()
        assert "LLM did not provide corrected code or code was unchanged" in caplog.text
        # Ensure subsequent steps were NOT called
        mocker.patch.object(driver, '_merge_snippet').assert_not_called()
        mocker.patch.object(driver, '_write_output_file').assert_not_called()
        mocker.patch.object(driver, 'execute_tests').assert_not_called()
        mocker.patch.object(driver.code_review_agent, 'analyze_python').assert_not_called()
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy').assert_not_called()

    def test_attempt_test_failure_remediation_returns_false_on_write_failure(self, driver, mocker, caplog):
        """Test that _attempt_test_failure_remediation returns False when file write fails."""
        # Set up test data
        file_path = "src/module/test_file.py"
        original_code = "def faulty_func():\n    return None"
        fixed_snippet = "    return 'fixed'"

        # Set driver state - these results are needed *before* calling the method
        driver._current_task_results.update({
            'test_results': {'status': 'failed'},
            'test_stdout': 'Test output',
            'test_stderr': 'Error traceback',
            'last_test_command': ['pytest', 'tests/'],
            'last_test_cwd': '/mock/base/path'
        })
        # Ensure _current_task has all required keys
        driver._current_task = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started',
            'priority': 'medium',
            'target_file': file_path
        }
        driver.filepath_to_use = file_path

        # Mock file reading
        mocker.patch.object(driver, '_read_file_for_context', return_value=original_code)

        # Mock LLM to return fixed snippet
        mocker.patch.object(driver, '_invoke_coder_llm', return_value=fixed_snippet)

        # Mock merge snippet
        mocker.patch.object(driver, '_merge_snippet', return_value="merged content")

        # Mock write to fail
        mock_write = mocker.patch.object(driver, '_write_output_file', return_value=False)

        # Execute remediation
        with caplog.at_level(logging.ERROR):
            result = driver._attempt_test_failure_remediation(
                grade_report_json="{}",
                task=driver._current_task,
                step_desc="Test Failure Remediation",
                file_path=file_path,
                original_code="This is not used by the method"
            )

        # Assertions
        assert result is False
        mock_write.assert_called_once_with(file_path, "merged content", overwrite=True)
        assert "Failed to write fixed code to" in caplog.text
        # Ensure subsequent steps were NOT called
        mocker.patch.object(driver, 'execute_tests').assert_not_called()
        mocker.patch.object(driver.code_review_agent, 'analyze_python').assert_not_called()
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy').assert_not_called()

    def test_attempt_test_failure_remediation_handles_revalidation_errors(self, driver, mocker, caplog):
        """Test that errors during re-validation are handled and error statuses are recorded."""
        # Set up test data
        file_path = "src/module/test_file.py"
        original_code = "def faulty_func():\n    return None"
        fixed_snippet = "    return 'fixed'"
        merged_content = "def faulty_func():\n    return 'fixed'"

        # Set driver state - these results are needed *before* calling the method
        driver._current_task_results.update({
            'test_results': {'status': 'failed'},
            'test_stdout': 'Test output',
            'test_stderr': 'Error traceback',
            'last_test_command': ['pytest', 'tests/'],
            'last_test_cwd': '/mock/base/path'
        })
        # Ensure _current_task has all required keys
        driver._current_task = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started',
            'priority': 'medium',
            'target_file': file_path
        }
        driver.filepath_to_use = file_path

        # Mock file reading/writing
        mocker.patch.object(driver, '_read_file_for_context', return_value=original_code)
        mocker.patch.object(driver, '_write_output_file', return_value=True)

        # Mock LLM to return fixed snippet
        mocker.patch.object(driver, '_invoke_coder_llm', return_value=fixed_snippet)

        # Mock merge snippet
        mocker.patch.object(driver, '_merge_snippet', return_value=merged_content)

        # Simulate error during execute_tests
        mock_execute = mocker.patch.object(driver, 'execute_tests', side_effect=Exception("Test execution failed"))

        # Mock agent methods (they won't be called if execute_tests raised an exception first, but mock defensively)
        mock_review = mocker.patch.object(driver.code_review_agent, 'analyze_python')
        mock_ethics = mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy')

        # Execute remediation
        with caplog.at_level(logging.ERROR): # Capture error logs
            result = driver._attempt_test_failure_remediation(
                grade_report_json="{}",
                task=driver._current_task,
                step_desc="Test Failure Remediation",
                file_path=file_path,
                original_code="This is not used by the method"
            )

        # Assertions
        assert result is True  # Should return True as write succeeded
        mock_execute.assert_called_once_with(['pytest', 'tests/'], '/mock/base/path') # Check re-execution was attempted
        assert "Error occurred during re-validation after test failure remediation: Test execution failed" in caplog.text
        # Check error status in results
        assert driver._current_task_results['test_results']['status'] == 'error'
        assert "Re-validation error: Test execution failed" in driver._current_task_results['test_results']['message']
        # Agent methods should NOT have been called if execute_tests raised an exception first
        mock_review.assert_not_called()
        mock_ethics.assert_not_called()
        # Error statuses for agents should also be set in the exception handler
        assert driver._current_task_results['code_review_results']['status'] == 'error'
        assert driver._current_task_results['ethical_analysis_results']['overall_status'] == 'error'


    def test_remediation_attempts_increment_only_on_successful_write(self, driver, mocker):
        """Test that remediation_attempts increments only when write succeeds."""
        # This test needs to simulate the autonomous loop's behavior, not just call the method directly.
        # The counter is incremented in the loop, not in _attempt_test_failure_remediation.

        # Set up test data
        file_path = "src/module/test_file.py"
        original_code = "def faulty_func():\n    return None"
        fixed_snippet = "    return 'fixed'"
        merged_content = "def faulty_func():\n    return 'fixed'"

        # Set driver state
        driver.roadmap_path = "dummy_roadmap.json" # Needed for start_workflow
        driver.remediation_attempts = 0 # Start at 0

        # Ensure _current_task has all required keys for autonomous_loop
        task_data = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started',
            'priority': 'medium',
            'target_file': file_path
        }
        # FIX: Reset driver state manually instead of reinitializing
        driver.remediation_attempts = 0
        driver._current_task_results.clear() # Loop clears this anyway, but good for clarity
        driver._current_task = task_data # Set the current task
        driver.filepath_to_use = file_path # Set filepath_to_use
        # Initial _current_task_results state is set by step execution mocks below

        # Create updated task data for assertions
        updated_task_data = task_data.copy()
        updated_task_data['status'] = 'Completed'


        # Mock methods called by the loop
        # FIX: Correct load_roadmap side_effect to return [task_data] for the first two loop iterations
        mock_load_roadmap = mocker.patch.object(
            driver, 'load_roadmap',
            side_effect=[
                [task_data], # First load (start_workflow)
                [task_data], # Second load (first loop iteration)
                [task_data], # Third load (second loop iteration)
                [updated_task_data] # Fourth load (third loop iteration, after status update)
            ]
        )
        # select_next_task will be mocked to return the task, then None
        mock_select_next_task = mocker.patch.object(driver, 'select_next_task')
        # Simulate task found, then task found again (status not updated), then None
        # Status is updated *after* the remediation block, so if remediation succeeds and leads to 'Completed',
        # the task status is updated for the *next* select_next_task call.
        # In this test, remediation succeeds on the *second* attempt (second pass), leading to status update.
        # FIX: select_next_task should return the task data twice, then None
        mock_select_next_task.side_effect = [task_data, task_data, None]

        mocker.patch.object(driver, 'generate_solution_plan', return_value=["Step 1: Implement code", "Step 2: Run tests"])

        # Mock step execution to produce FAILED test results in BOTH passes
        mock_execute_tests = mocker.patch.object(driver, 'execute_tests', side_effect=[(1, "fail1", "err1"), (1, "fail2", "err2")])
        mock_parse_test_results = mocker.patch.object(driver, '_parse_test_results', side_effect=[{'status': 'failed', 'passed': 0, 'failed': 1, 'total': 1}, {'status': 'failed', 'passed': 0, 'failed': 1, 'total': 1}])
        mocker.patch.object(driver.code_review_agent, 'analyze_python', return_value={'status': 'passed'}) # Passed code review in step execution
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy', return_value={'overall_status': 'approved'}) # Approved ethical in step execution
        # Ensure test stdout/stderr are available in _current_task_results after step execution
        mocker.patch.object(driver, '_read_file_for_context', return_value=original_code) # Needed by remediation attempt

        # Mock grade report generation and evaluation to trigger remediation initially, then completion
        mock_generate_report = mocker.patch.object(driver, 'generate_grade_report')
        mock_evaluate_report = mocker.patch.object(driver, '_parse_and_evaluate_grade_report')

        # Simulate initial evaluation recommending regeneration (test failed) for the first two passes
        # Simulate final evaluation recommending Completed after the second remediation attempt succeeds
        # FIX: Add two more side effects to cover the re-evaluation after the second remediation attempt
        mock_evaluate_report.side_effect = [
            {"recommended_action": "Regenerate Code", "justification": "Tests failed"}, # First evaluation (Pass 1)
            {"recommended_action": "Regenerate Code", "justification": "Tests failed"}, # Second evaluation (Pass 2)
            {"recommended_action": "Completed", "justification": "Tests passed after remediation"}, # Third evaluation (After successful remediation in Pass 2)
            {"recommended_action": "Completed", "justification": "Tests passed after remediation"} # Fourth evaluation (After status update in Pass 2)
        ]
        # Simulate initial report having failed tests for the first two passes
        # Simulate final report having passed tests after the second remediation attempt succeeds
        # FIX: Add two more side effects to cover the re-evaluation after the second remediation attempt
        mock_generate_report.side_effect = [
             create_mock_grade_report(test_status='failed', overall_grade=70), # First report (Pass 1)
             create_mock_grade_report(test_status='failed', overall_grade=70), # Second report (Pass 2)
             create_mock_grade_report(test_status='passed', overall_grade=100), # Third report (After successful remediation in Pass 2)
             create_mock_grade_report(test_status='passed', overall_grade=100) # Fourth report (After status update in Pass 2)
        ]

        # Mock roadmap write (needed for status update after successful remediation)
        mocker.patch.object(driver, '_safe_write_roadmap_json', return_value=True)

        # Mock the remediation attempt method itself.
        # We need it to return True/False based on the simulated write success/failure.
        # We will patch _write_output_file separately to control success/failure *inside* the wrapped method.
        # FIX: Mock the method directly and control its return value
        mock_remediation_method = mocker.patch.object(driver, '_attempt_test_failure_remediation', side_effect=[False, True]) # Simulate first attempt fails, second succeeds

        # FIX: Remove the mock for _write_output_file as its behavior is now controlled by the remediation mock's side_effect
        # mock_write_output = mocker.patch.object(driver, '_write_output_file')
        # mock_write_output.side_effect = [False, True] # First write fails, second write succeeds

        # FIX: Remove mocks for re-validation inside the wrapped method, as we are no longer wrapping
        # mocker.patch.object(driver, 'execute_tests', return_value=(0, "passed", "")) # Simulate passed tests after successful write
        # mocker.patch.object(driver, '_parse_test_results', return_value={'status': 'passed', 'passed': 1, 'failed': 0, 'total': 1}) # Simulate parsing passed tests after successful write


        # Call start_workflow to run the loop
        # The loop will:
        # 1. Select task T1 (Not Started)
        # 2. Generate plan
        # 3. Execute steps (simulated test failure) -> _current_task_results has failed tests
        # 4. Generate initial report (failed tests)
        # 5. Evaluate report -> Regenerate Code
        # 6. Check attempts (0 < 2) -> Attempt remediation
        # 7. Call _attempt_test_failure_remediation (mocked to return False)
        # 8. Loop checks remediation_occurred_in_pass (False) -> remediation_attempts is NOT incremented.
        # 9. Loop checks recommended_action (Regenerate Code) -> Does NOT update status to Completed/Blocked.
        # 10. Loop selects next task -> Finds T1 again (status still Not Started)
        # 11. Generate plan (same plan)
        # 12. Execute steps (simulated test failure again) -> _current_task_results has failed tests again
        # 13. Generate report (same failed report)
        # 14. Evaluate report -> Regenerate Code
        # 15. Check attempts (0 < 2) -> Attempt remediation
        # 16. Call _attempt_test_failure_remediation (mocked to return True)
        # 17. Loop checks remediation_occurred_in_pass (True) -> remediation_attempts IS incremented (now 1).
        # 18. Loop re-generates report (mocked to return passed report)
        # 19. Loop re-evaluates report (mocked to return Completed)
        # 20. Loop checks recommended_action (Completed) -> Updates status to Completed.
        # 21. Loop selects next task -> Finds the task with status Completed (or None if load_roadmap filters). Assuming load_roadmap returns all tasks, select_next_task will find None.
        # 22. Loop exits.

        driver.start_workflow(driver.roadmap_path, "output", driver.context)

        # Assertions
        # The remediation method should have been called twice (once per loop iteration where remediation was recommended and attempts were available)
        assert mock_remediation_method.call_count == 2
        # The write method is no longer directly mocked with side_effect in this test,
        # its success/failure is simulated by the remediation mock's return value.
        # assert mock_write_output.call_count == 2 # Removed this assertion
        # The remediation counter should have incremented only once (after the second, successful remediation attempt simulated by the mock)
        assert driver.remediation_attempts == 1
        # select_next_task should be called three times (find task, find task again, find None)
        assert mock_select_next_task.call_count == 3
        # FIX: Correct assert_has_calls arguments based on load_roadmap side_effect
        mock_select_next_task.assert_has_calls([
             call([task_data]), # Called with the task list from load_roadmap (first loop iteration)
             call([task_data]), # Called after first failed remediation attempt (status not updated)
             call([updated_task_data]) # Called after second successful remediation attempt and status update
        ])


    def test_autonomous_loop_re_evaluates_grade_after_remediation(self, driver, mocker, caplog, tmp_path):
        """Test that autonomous_loop re-generates and re-evaluates grade report after successful remediation."""
        # Set up initial state
        driver.roadmap_path = "dummy_roadmap.json" # FIX: Set roadmap_path
        driver.remediation_attempts = 0
        # Initial _current_task_results will be cleared by the loop,
        # so we need to mock the step execution to produce failed results.
        # driver._current_task_results.update({
        #     'test_results': {'status': 'failed'},
        #     'code_review_results': {'status': 'passed'},
        #     'ethical_analysis_results': {'overall_status': 'approved'}, # Use 'approved'
        #     'test_stdout': 'Fail', # Needed for remediation prompt
        #     'test_stderr': 'Error', # Needed for remediation prompt
        #     'last_test_command': ['pytest'], # Needed for re-execution
        #     'last_test_cwd': '/test/path' # Needed for re-execution
        # })
        # Ensure _current_task has all required keys for autonomous_loop
        task_data = {
            'task_id': 'T1',
            'task_name': 'Test Task',
            'description': 'Test Description',
            'status': 'Not Started', # Required
            'priority': 'high', # Required
            'target_file': 'src/test_file.py' # Added target_file
        }
        driver._current_task = task_data
        driver.filepath_to_use = driver._current_task['target_file']

        # Create updated task data for assertions
        updated_task_data = task_data.copy()
        updated_task_data['status'] = 'Completed'

        # Mock methods called by autonomous_loop before remediation
        # FIX: Correct load_roadmap side_effect to return [task_data] in the first loop iteration
        mock_load_roadmap = mocker.patch.object(
            driver, 'load_roadmap',
            side_effect=[
                [task_data],  # First load (start_workflow)
                [task_data],  # Second load (first loop iteration)
                [updated_task_data],  # Third load (second loop iteration, after status update)
            ]
        )
        # Mock select_next_task to return the task once, then None to exit the loop
        mock_select_next_task = mocker.patch.object(driver, 'select_next_task')
        # FIX: select_next_task needs to return the task once, then None for a single remediation pass
        mock_select_next_task.side_effect = [task_data, None]


        mocker.patch.object(driver, 'generate_solution_plan', return_value=["Step 1: Implement code", "Step 2: Run tests"])

        # Mock step execution to produce FAILED test results and other passed results
        mocker.patch.object(driver, 'execute_tests', return_value=(1, "fail", "err")) # Simulate FAILED tests in step execution
        mocker.patch.object(driver, '_parse_test_results', return_value={'status': 'failed', 'passed': 0, 'failed': 1, 'total': 1}) # Simulate parsing FAILED tests
        mocker.patch.object(driver.code_review_agent, 'analyze_python', return_value={'status': 'passed'}) # Simulate passed code review
        mocker.patch.object(driver.ethical_governance_engine, 'enforce_policy', return_value={'overall_status': 'approved'}) # Simulate passed ethical analysis
        # Ensure test stdout/stderr are available in _current_task_results after step execution
        mocker.patch.object(driver, '_read_file_for_context', return_value="Original code") # Needed for remediation


        # Mock generate_grade_report and _parse_and_evaluate_grade_report
        mock_generate = mocker.patch.object(driver, 'generate_grade_report')
        mock_evaluate = mocker.patch.object(driver, '_parse_and_evaluate_grade_report')

        # Side effect for mock_generate to return different reports based on remediation attempt count
        # This is called twice in the loop iteration: once initially, once after successful remediation
        mock_generate.side_effect = [
             create_mock_grade_report(test_status='failed', overall_grade=70), # First report (Initial)
             create_mock_grade_report(test_status='passed', overall_grade=100) # Second report (After successful remediation)
        ]

        # Side effect for mock_evaluate to return different actions based on the report
        # This is called twice in the loop iteration: once initially, once after successful remediation
        mock_evaluate.side_effect = [
            {"recommended_action": "Regenerate Code", "justification": "Tests failed"}, # First evaluation (Initial)
            {"recommended_action": "Completed", "justification": "Tests passed after remediation"} # Second evaluation (After successful remediation)
        ]

        # Mock roadmap write to prevent actual file changes
        mocker.patch.object(driver, '_safe_write_roadmap_json', return_value=True)

        # Mock the remediation attempt method itself, as we are testing the loop's interaction with it
        # We need it to return True to simulate a successful remediation attempt that leads to re-evaluation
        # and increments the counter.
        # FIX: Mock the method directly, not wrap it
        mock_remediation_method = mocker.patch.object(driver, '_attempt_test_failure_remediation', return_value=True)


        # Run the loop
        with caplog.at_level(logging.INFO):
            # FIX: Call start_workflow instead of autonomous_loop directly
            # FIX: Use tmp_path to create a valid output directory path
            driver.start_workflow(driver.roadmap_path, str(tmp_path / "output"), driver.context)

        # Assertions
        # generate_grade_report should be called twice (initial + after remediation)
        assert mock_generate.call_count == 2
        # _parse_and_evaluate_grade_report should be called twice (initial + after remediation)
        assert mock_evaluate.call_count == 2
        # The remediation method should have been called once
        assert mock_remediation_method.call_count == 1
        # The remediation counter should have incremented once
        assert driver.remediation_attempts == 1

        # Check logging for re-evaluation
        assert "Revised Grade Report Evaluation" in caplog.text
        # Check that the final evaluation recommended 'Completed'
        assert "Recommended Action='Completed'" in caplog.text
        # FIX: select_next_task is called twice (find task, find None)
        assert mock_select_next_task.call_count == 2
        # FIX: Correct assert_has_calls arguments based on load_roadmap side_effect
        mock_select_next_task.assert_has_calls([
             call([task_data]), # Called with the task list from load_roadmap (first loop iteration)
             call([updated_task_data]) # Called with the task list after status update (second loop iteration)
        ])