import pytest
import json
from unittest.mock import MagicMock, patch, ANY, call
from src.core.automation.workflow_driver import WorkflowDriver, Context
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from pathlib import Path
import logging

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with mocked dependencies for testing remediation
@pytest.fixture
def test_driver_remediation(tmp_path):
    # Create dummy policy file
    dummy_policy_dir = tmp_path / "policies"
    dummy_policy_dir.mkdir()
    dummy_policy_path = dummy_policy_dir / "policy_bias_risk_strict.json"
    dummy_policy_content = {"policy_name": "Mock Policy", "rules": []}
    with open(dummy_policy_path, "w") as f:
        json.dump(dummy_policy_content, f)

    # Create ROADMAP.json with a valid task structure
    roadmap_path = tmp_path / "ROADMAP.json"
    # *** FIX APPLIED HERE: Add 'target_file' to initial_task in the file ***
    initial_task = {
        "task_id": "test_task_1",
        "priority": "High",
        "task_name": "Test Task",
        "status": "Not Started",
        "description": "Desc",
        "depends_on": [],
        "target_file": "src/test_file.py" # Added target_file here
    }
    with open(roadmap_path, "w") as f:
        json.dump({"tasks": [initial_task]}, f)

    context = Context(str(tmp_path))

    # Patch dependencies
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:

        mock_code_review_agent = MockCodeReviewAgent.return_value
        mock_ethical_engine = MockEthicalGovernanceEngine.return_value
        mock_ethical_engine.load_policy_from_json.return_value = dummy_policy_content

        driver = WorkflowDriver(context)
        driver.llm_orchestrator = MagicMock()

        # Replace methods with mocks
        driver.load_roadmap = MagicMock(side_effect=lambda path: json.load(open(driver.context.get_full_path(path))).get("tasks", []))
        driver.select_next_task = MagicMock()
        driver.generate_solution_plan = MagicMock()
        driver._read_file_for_context = MagicMock()
        driver._invoke_coder_llm = MagicMock()
        driver._merge_snippet = MagicMock()
        driver._write_output_file = MagicMock()
        driver.execute_tests = MagicMock()
        driver._parse_test_results = MagicMock()

        # These will be used as-is (with mocked return values)
        driver.generate_grade_report = MagicMock()
        driver._parse_and_evaluate_grade_report = MagicMock()
        driver._safe_write_roadmap_json = MagicMock()
        driver._run_post_write_validation = MagicMock()
        driver._check_if_remediation_needed = MagicMock()
        driver._build_remediation_prompt = MagicMock()

        driver.roadmap_path = "ROADMAP.json"
        driver.context = context

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent,
            'mock_ethical_governance_engine': mock_ethical_engine,
            'mock_llm_orchestrator': driver.llm_orchestrator,
            'mock_load_roadmap': driver.load_roadmap,
            'mock_select_next_task': driver.select_next_task,
            'mock_generate_solution_plan': driver.generate_solution_plan,
            'mock_read_file_for_context': driver._read_file_for_context,
            'mock_invoke_coder_llm': driver._invoke_coder_llm,
            'mock_merge_snippet': driver._merge_snippet,
            'mock_write_output_file': driver._write_output_file,
            'mock_execute_tests': driver.execute_tests,
            'mock_parse_test_results': driver._parse_test_results,
            'mock_generate_grade_report': driver.generate_grade_report,
            'mock_parse_and_evaluate_grade_report': driver._parse_and_evaluate_grade_report,
            'mock_safe_write_roadmap_json': driver._safe_write_roadmap_json,
            'mock_run_post_write_validation': driver._run_post_write_validation,
            'mock_check_if_remediation_needed': driver._check_if_remediation_needed,
            'mock_build_remediation_prompt': driver._build_remediation_prompt,
        }


class TestWorkflowRemediation:

    # *** FIX APPLIED HERE: Add target_file parameter with default to setup_task_and_plan ***
    def setup_task_and_plan(self, mocks, task_id="test_task_1", status="Not Started", target_file="src/test_file.py", plan_steps=None):
        task = {
            'task_id': task_id,
            'priority': 'High',
            'task_name': 'Test Task',
            'status': status,
            'description': 'Desc',
            'target_file': target_file, # Ensure this is included in the task dict returned by the mock
            'depends_on': []
        }

        mocks['mock_select_next_task'].side_effect = [task, None]
        mocks['mock_generate_solution_plan'].return_value = plan_steps if plan_steps is not None else ["Step 1: Implement code in src/test_file.py"]
        mocks['mock_safe_write_roadmap_json'].return_value = True

        return task

    # Test Case 1: Code Style remediation success on first attempt
    def test_remediation_code_style_success_first_attempt(self, test_driver_remediation, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_remediation['driver']
        mocks = test_driver_remediation

        task = self.setup_task_and_plan(mocks)

        mocks['mock_read_file_for_context'].side_effect = ["Existing content", "Merged content"]
        mocks['mock_invoke_coder_llm'].side_effect = ["Generated snippet", "Remediated snippet"]
        mocks['mock_merge_snippet'].side_effect = ["Merged content", "Remediated merged content 1"]
        mocks['mock_write_output_file'].return_value = True
        mocks['mock_run_post_write_validation'].return_value = None

        initial_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "code_review": {
                    "status": "failed",
                    "static_analysis": [{"severity": "error", "code": "E001", "message": "Style issue"}]
                }
            }
        })
        remediation_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 100},
            "validation_results": {}
        })
        initial_evaluation = {"recommended_action": "Regenerate Code", "justification": "Style issues found."}
        remediation_evaluation = {"recommended_action": "Completed", "justification": "Remediation successful."}

        mocks['mock_generate_grade_report'].side_effect = [initial_grade_report, remediation_grade_report]
        # The NameError was reported here, but the definitions are above.
        # Assuming the code is as provided, this line is correct.
        mocks['mock_parse_and_evaluate_grade_report'].side_effect = [initial_evaluation, remediation_evaluation]
        mocks['mock_check_if_remediation_needed'].side_effect = [(True, "Code Style", "Style feedback"), (False, None, None)]
        mocks['mock_build_remediation_prompt'].return_value = "Remediation prompt"

        driver.start_workflow("ROADMAP.json", "dummy_output_dir", driver.context)

        expected_task = {
            'task_id': 'test_task_1',
            'task_name': 'Test Task',
            'status': 'Completed',
            'description': 'Desc',
            'priority': 'High',
            'target_file': 'src/test_file.py', # This key is now expected
            'depends_on': []
        }

        mocks['mock_safe_write_roadmap_json'].assert_called_once_with(ANY, {'tasks': [expected_task]})


    # Test Case 2: Ethical Transparency remediation success on first attempt
    def test_remediation_transparency_success_first_attempt(self, test_driver_remediation, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_remediation['driver']
        mocks = test_driver_remediation

        task = self.setup_task_and_plan(mocks)

        mocks['mock_read_file_for_context'].side_effect = ["Existing content", "Merged content"]
        mocks['mock_invoke_coder_llm'].side_effect = ["Generated snippet", "Remediated snippet"]
        mocks['mock_merge_snippet'].side_effect = ["Merged content", "Remediated merged content 1"]
        mocks['mock_write_output_file'].return_value = True
        mocks['mock_run_post_write_validation'].return_value = None

        initial_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 85},
            "validation_results": {
                "ethical_analysis": {
                    "overall_status": "rejected",
                    "TransparencyScore": {"status": "violation", "details": "Missing docstring"}
                }
            }
        })
        initial_evaluation = {"recommended_action": "Regenerate Code", "justification": "Ethical issues found."}
        remediation_grade_report = json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}})
        remediation_evaluation = {"recommended_action": "Completed", "justification": "Remediation successful."}

        mocks['mock_generate_grade_report'].side_effect = [initial_grade_report, remediation_grade_report]
        mocks['mock_parse_and_evaluate_grade_report'].side_effect = [initial_evaluation, remediation_evaluation]
        mocks['mock_check_if_remediation_needed'].side_effect = [
            (True, "Ethical Transparency", "Missing docstring"),
            (False, None, None)
        ]
        mocks['mock_build_remediation_prompt'].return_value = "Remediation prompt"

        driver.start_workflow("ROADMAP.json", "dummy_output_dir", driver.context)

        expected_task = {
            'task_id': 'test_task_1',
            'task_name': 'Test Task',
            'status': 'Completed',
            'description': 'Desc',
            'priority': 'High',
            'target_file': 'src/test_file.py', # This key is now expected
            'depends_on': []
        }

        mocks['mock_safe_write_roadmap_json'].assert_called_once_with(ANY, {'tasks': [expected_task]})


    # Test Case 3: Remediation success on second attempt
    def test_remediation_success_second_attempt(self, test_driver_remediation, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_remediation['driver']
        mocks = test_driver_remediation

        task = self.setup_task_and_plan(mocks)

        mocks['mock_read_file_for_context'].side_effect = ["Existing content", "Merged content", "Remediated merged content 1"]
        mocks['mock_invoke_coder_llm'].side_effect = ["Generated snippet", "Remediated snippet 1", "Remediated snippet 2"]
        mocks['mock_merge_snippet'].side_effect = ["Merged content", "Remediated merged content 1", "Remediated merged content 2"]
        mocks['mock_write_output_file'].return_value = True
        mocks['mock_run_post_write_validation'].return_value = None

        initial_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "code_review": {
                    "status": "failed",
                    "static_analysis": [{"severity": "error", "code": "E001", "message": "Style issue"}]
                }
            }
        })
        attempt1_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "code_review": {
                    "status": "failed",
                    "static_analysis": [{"severity": "error", "code": "E001", "message": "Style issue"}]
                }
            }
        })
        attempt2_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 100},
            "validation_results": {}
        })

        initial_evaluation = {"recommended_action": "Regenerate Code", "justification": "Style issues found."}
        attempt1_evaluation = {"recommended_action": "Regenerate Code", "justification": "Still style issues."}
        attempt2_evaluation = {"recommended_action": "Completed", "justification": "Remediation successful."}

        mocks['mock_generate_grade_report'].side_effect = [initial_grade_report, attempt1_grade_report, attempt2_grade_report]
        mocks['mock_parse_and_evaluate_grade_report'].side_effect = [initial_evaluation, attempt1_evaluation, attempt2_evaluation]
        mocks['mock_check_if_remediation_needed'].side_effect = [
            (True, "Code Style", "Style feedback 1"),
            (True, "Code Style", "Style feedback 2"),
            (False, None, None)
        ]
        mocks['mock_build_remediation_prompt'].side_effect = ["Remediation prompt 1", "Remediation prompt 2"]

        driver.start_workflow("ROADMAP.json", "dummy_output_dir", driver.context)

        expected_task = {
            'task_id': 'test_task_1',
            'task_name': 'Test Task',
            'status': 'Completed',
            'description': 'Desc',
            'priority': 'High',
            'target_file': 'src/test_file.py', # This key is now expected
            'depends_on': []
        }

        mocks['mock_safe_write_roadmap_json'].assert_called_once_with(ANY, {'tasks': [expected_task]})


    # Test Case 4: Remediation max attempts reached
    def test_remediation_max_attempts_reached(self, test_driver_remediation, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_remediation['driver']
        mocks = test_driver_remediation

        task = self.setup_task_and_plan(mocks)

        mocks['mock_read_file_for_context'].side_effect = ["Existing content", "Merged content", "Remediated merged content 1"]
        mocks['mock_invoke_coder_llm'].side_effect = ["Generated snippet", "Remediated snippet 1", "Remediated snippet 2"]
        mocks['mock_merge_snippet'].side_effect = ["Merged content", "Remediated merged content 1", "Remediated merged content 2"]
        mocks['mock_write_output_file'].return_value = True
        mocks['mock_run_post_write_validation'].return_value = None

        initial_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "code_review": {
                    "status": "failed",
                    "static_analysis": [{"severity": "error", "code": "E001", "message": "Style issue"}]
                }
            }
        })
        attempt1_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "code_review": {
                    "status": "failed",
                    "static_analysis": [{"severity": "error", "code": "E001", "message": "Style issue"}]
                }
            }
        })
        attempt2_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "code_review": {
                    "status": "failed",
                    "static_analysis": [{"severity": "error", "code": "E001", "message": "Style issue"}]
                }
            }
        })

        initial_evaluation = {"recommended_action": "Regenerate Code", "justification": "Style issues found."}
        attempt1_evaluation = {"recommended_action": "Regenerate Code", "justification": "Still style issues."}
        attempt2_evaluation = {"recommended_action": "Regenerate Code", "justification": "Still style issues."}

        mocks['mock_generate_grade_report'].side_effect = [initial_grade_report, attempt1_grade_report, attempt2_grade_report]
        mocks['mock_parse_and_evaluate_grade_report'].side_effect = [initial_evaluation, attempt1_evaluation, attempt2_evaluation]
        mocks['mock_check_if_remediation_needed'].side_effect = [
            (True, "Code Style", "Style feedback 1"),
            (True, "Code Style", "Style feedback 2"),
            # This won't be reached because max attempts is 2 and the loop breaks
            (False, None, None)
        ]
        mocks['mock_build_remediation_prompt'].side_effect = ["Remediation prompt 1", "Remediation prompt 2"]

        driver.start_workflow("ROADMAP.json", "dummy_output_dir", driver.context)

        # The task status should NOT be updated to "Completed" because remediation failed
        # and the final evaluation was "Regenerate Code".
        # The driver's logic currently doesn't explicitly set status to "Blocked" or leave it "Not Started"
        # if remediation fails after max attempts, but it definitely shouldn't set it to "Completed".
        # So, assert that safe_write_roadmap_json was NOT called to update the status to Completed.
        # It might be called if the logic were to set it to "Blocked", but based on the trace, it wasn't called at all.
        mocks['mock_safe_write_roadmap_json'].assert_not_called()


    # Test Case 5: Remediation not triggered for test failure
    def test_remediation_not_triggered_for_test_failure(self, test_driver_remediation, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_remediation['driver']
        mocks = test_driver_remediation

        # Pass plan_steps explicitly to include the test step
        task = self.setup_task_and_plan(mocks, plan_steps=["Step 1: Implement code in src/test_file.py", "Step 2: Run tests"])

        mocks['mock_read_file_for_context'].side_effect = ["Existing content"]
        mocks['mock_invoke_coder_llm'].return_value = "Generated snippet"
        mocks['mock_merge_snippet'].return_value = "Merged content"
        mocks['mock_write_output_file'].return_value = True
        mocks['mock_run_post_write_validation'].return_value = None

        mocks['mock_execute_tests'].return_value = (1, "Pytest output", "Errors")
        mocks['mock_parse_test_results'].return_value = {
            'status': 'failed', 'passed': 0, 'failed': 1, 'total': 1, 'message': 'Parsed successfully.'
        }

        initial_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 70},
            "validation_results": {"tests": {"status": "failed", "failed": 1}}
        })
        initial_evaluation = {"recommended_action": "Regenerate Code", "justification": "Automated tests failed."}
        mocks['mock_generate_grade_report'].return_value = initial_grade_report
        mocks['mock_parse_and_evaluate_grade_report'].return_value = initial_evaluation
        # Remediation check should return False for test failures
        mocks['mock_check_if_remediation_needed'].return_value = (False, None, None)

        driver.start_workflow("ROADMAP.json", "dummy_output_dir", driver.context)

        # Assertions to confirm remediation was NOT attempted
        mocks['mock_check_if_remediation_needed'].assert_called_once_with(initial_grade_report)
        mocks['mock_build_remediation_prompt'].assert_not_called()
        mocks['mock_invoke_coder_llm'].assert_called_once() # Coder LLM was called for initial code gen
        mocks['mock_write_output_file'].assert_called_once() # File was written initially

        # The task status should NOT be updated to "Completed" because tests failed
        # and the final evaluation was "Regenerate Code".
        mocks['mock_safe_write_roadmap_json'].assert_not_called()


    # Test Case 6: Remediation not triggered for success
    def test_remediation_not_triggered_for_success(self, test_driver_remediation, caplog):
        caplog.set_level(logging.INFO)
        driver = test_driver_remediation['driver']
        mocks = test_driver_remediation

        task = self.setup_task_and_plan(mocks)

        mocks['mock_read_file_for_context'].side_effect = ["Existing content"]
        mocks['mock_invoke_coder_llm'].return_value = "Generated snippet"
        mocks['mock_merge_snippet'].return_value = "Merged content"
        mocks['mock_write_output_file'].return_value = True
        mocks['mock_run_post_write_validation'].return_value = None

        initial_grade_report = json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}})
        initial_evaluation = {"recommended_action": "Completed", "justification": "Overall grade is 100%."}
        mocks['mock_generate_grade_report'].return_value = initial_grade_report
        mocks['mock_parse_and_evaluate_grade_report'].return_value = initial_evaluation
        # Remediation check should return False for success
        mocks['mock_check_if_remediation_needed'].return_value = (False, None, None)

        driver.start_workflow("ROADMAP.json", "dummy_output_dir", driver.context)

        # Assertions to confirm remediation was NOT attempted
        mocks['mock_check_if_remediation_needed'].assert_called_once_with(initial_grade_report)
        mocks['mock_build_remediation_prompt'].assert_not_called()
        mocks['mock_invoke_coder_llm'].assert_called_once() # Coder LLM was called for initial code gen
        mocks['mock_write_output_file'].assert_called_once() # File was written initially

        expected_task = {
            'task_id': 'test_task_1',
            'task_name': 'Test Task',
            'status': 'Completed',
            'description': 'Desc',
            'priority': 'High',
            'target_file': 'src/test_file.py', # This key is now expected
            'depends_on': []
        }

        mocks['mock_safe_write_roadmap_json'].assert_called_once_with(ANY, {'tasks': [expected_task]})


    # Test Case 7: Remediation prompt content verification
    def test_remediation_prompt_content(self, test_driver_remediation, caplog):
        caplog.set_level(logging.DEBUG)
        driver = test_driver_remediation['driver']
        mocks = test_driver_remediation

        task = self.setup_task_and_plan(mocks)

        mocks['mock_read_file_for_context'].side_effect = ["Existing content", "Merged content"]
        mocks['mock_invoke_coder_llm'].side_effect = ["Generated snippet", "Remediated snippet"]
        mocks['mock_merge_snippet'].side_effect = ["Merged content", "Remediated merged content"]
        mocks['mock_write_output_file'].return_value = True
        mocks['mock_run_post_write_validation'].return_value = None

        initial_grade_report = json.dumps({
            "grades": {"overall_percentage_grade": 90},
            "validation_results": {
                "code_review": {
                    "status": "failed",
                    "static_analysis": [{
                        "severity": "error",
                        "code": "E001",
                        "message": "Style issue",
                        "file": "src/test_file.py",
                        "line": "1",
                        "col": "1"
                    }]
                }
            }
        })
        initial_evaluation = {"recommended_action": "Regenerate Code", "justification": "Style issues found."}
        remediation_grade_report = json.dumps({"grades": {"overall_percentage_grade": 100}, "validation_results": {}})
        remediation_evaluation = {"recommended_action": "Completed", "justification": "Remediation successful."}

        mocks['mock_generate_grade_report'].side_effect = [initial_grade_report, remediation_grade_report]
        mocks['mock_parse_and_evaluate_grade_report'].side_effect = [initial_evaluation, remediation_evaluation]
        mocks['mock_check_if_remediation_needed'].side_effect = [
            (True, "Code Style", "Please fix the following code style issues:\n- src/test_file.py:1:1: E001 Style issue"),
            (False, None, None)
        ]
        mocks['mock_build_remediation_prompt'].return_value = "Remediation prompt"

        expected_task = {
            'task_id': 'test_task_1',
            'task_name': 'Test Task',
            'status': 'Not Started', # Status is 'Not Started' when passed to build_remediation_prompt
            'description': 'Desc',
            'priority': 'High',
            'target_file': 'src/test_file.py', # This key is now expected
            'depends_on': []
        }

        driver.start_workflow("ROADMAP.json", "dummy_output_dir", driver.context)

        mocks['mock_build_remediation_prompt'].assert_called_once_with(
            task=expected_task,
            target_file="src/test_file.py",
            original_code="Merged content",
            feedback="Please fix the following code style issues:\n- src/test_file.py:1:1: E001 Style issue",
            remediation_type="Code Style"
        )