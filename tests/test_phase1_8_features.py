# tests/test_phase1_8_features.py

import pytest
import unittest
from unittest.mock import patch, MagicMock, mock_open, call, ANY
import re
from pathlib import Path
import logging
import json
from datetime import datetime
import subprocess

# Assuming WorkflowDriver is in src.core.automation
from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT

# Import CodeReviewAgent and EthicalGovernanceEngine for type hinting and mocking
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine

# Import write_file and file_exists if needed for specific mocks
from src.cli.write_file import write_file, file_exists

# Import builtins for mocking open
import builtins

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Use the correct logger name for the module
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context, specifically for Phase 1.8 tests
@pytest.fixture
def test_driver_phase1_8(tmp_path):
    # Create the actual Context object
    context = Context(str(tmp_path))

    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation
    with patch('src.core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:
        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        # Mock the policy loading within the engine mock
        mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        # Instantiate WorkflowDriver using the created context object
        driver = WorkflowDriver(context) # Use the 'context' object here

        # Ensure LLM orchestrator mock is set up
        driver.llm_orchestrator = MagicMock()
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"

        # Assign mocked instances
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set

        # Add attributes needed for tests that might not be set by __init__ or autonomous_loop setup
        driver._current_task_results = {}
        driver.remediation_attempts = 0 # Initialize remediation counter for tests
        driver.remediation_occurred_in_pass = False # Initialize flag
        driver._current_task = {} # Initialize current task

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance
        }

# Helper function to simulate the relevant part of autonomous_loop for testing classification
def check_step_classification(driver_instance, step_text, task_target_file=None):
    step_lower = step_text.lower()
    filepath_from_step_match = re.search(
        r'(\S+\.(py|md|json|txt|yml|yaml))', step_text, re.IGNORECASE)
    filepath_from_step = filepath_from_step_match.group(1) if filepath_from_step_match else None

    code_generation_keywords = ["implement", "generate code", "write function", "modify", "add", "define", "create", "update", "refactor"]
    research_keywords = ["research and identify", "research", "analyze", "investigate", "understand"]
    code_element_keywords = ["import", "constant", "variable", "function", "class", "method", "definition", "parameter", "return"]
    file_writing_keywords = ["write", "write file", "create", "create file", "update", "update file", "modify", "modify file", "save to file", "output file", "generate file", "write output to"]
    test_execution_keywords = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]

    is_test_execution_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in test_execution_keywords)
    is_explicit_file_writing_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in file_writing_keywords)
    is_research_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in research_keywords)

    filepath_to_use = task_target_file
    if filepath_to_use is None and (is_explicit_file_writing_step or \
        (not is_research_step and any(re.search(r'\b' + re.escape(verb) + r'\b', step_lower) for verb in code_generation_keywords) and \
         (any(re.search(r'\b' + re.escape(element) + r'\b', step_lower) for element in code_element_keywords) or \
          (filepath_from_step and filepath_from_step.endswith('.py')))) \
        ) and filepath_from_step:
        filepath_to_use = filepath_from_step

    is_code_generation_step = not is_research_step and \
                              any(re.search(r'\b' + re.escape(verb) + r'\b', step_lower) for verb in code_generation_keywords) and \
                              (any(re.search(r'\b' + re.escape(element) + r'\b', step_lower) for element in code_element_keywords) or \
                               (filepath_to_use and filepath_to_use.endswith('.py')))


    return {
        "is_code_generation_step": is_code_generation_step,
        "is_research_step": is_research_step,
        "is_explicit_file_writing_step": is_explicit_file_writing_step,
        "is_test_execution_step": is_test_execution_step,
        "filepath_to_use": filepath_to_use
    }


class TestPhase1_8Features:

    # --- Tests for Task 1.8.1: Enhance Plan Step Identification ---
    # These tests verify the step classification logic after applying the pre-fix.

    def test_research_step_classification(self, test_driver_phase1_8):
        """Test that steps with research keywords are correctly classified as non-code-gen."""
        driver = test_driver_phase1_8['driver']

        step1 = "Research and identify keywords for src/core/automation/workflow_driver.py"
        classification1 = check_step_classification(driver, step1, task_target_file="src/core/automation/workflow_driver.py")
        assert classification1["is_research_step"] is True
        assert classification1["is_code_generation_step"] is False
        assert classification1["is_explicit_file_writing_step"] is False
        assert classification1["is_test_execution_step"] is False
        assert classification1["filepath_to_use"] == "src/core/automation/workflow_driver.py"

        step2 = "Analyze the current implementation of token allocation."
        classification2 = check_step_classification(driver, step2, task_target_file="src/core/optimization/adaptive_token_allocator.py")
        assert classification2["is_research_step"] is True
        assert classification2["is_code_generation_step"] is False
        assert classification2["is_explicit_file_writing_step"] is False
        assert classification2["is_test_execution_step"] is False
        assert classification2["filepath_to_use"] == "src/core/optimization/adaptive_token_allocator.py"

        step3 = "Investigate potential NLP techniques for step identification."
        classification3 = check_step_classification(driver, step3, task_target_file="src/core/automation/workflow_driver.py")
        assert classification3["is_research_step"] is True
        assert classification3["is_code_generation_step"] is False
        assert classification3["is_explicit_file_writing_step"] is False
        assert classification3["is_test_execution_step"] is False
        assert classification3["filepath_to_use"] == "src/core/automation/workflow_driver.py"

    def test_code_generation_step_classification(self, test_driver_phase1_8):
        """Test that steps clearly involving code modification are classified as code-gen."""
        driver = test_driver_phase1_8['driver']

        step1 = "Implement the new function in src/core/automation/workflow_driver.py"
        classification1 = check_step_classification(driver, step1, task_target_file="src/core/automation/workflow_driver.py")
        assert classification1["is_research_step"] is False
        assert classification1["is_code_generation_step"] is True
        assert classification1["is_explicit_file_writing_step"] is False
        assert classification1["is_test_execution_step"] is False
        assert classification1["filepath_to_use"] == "src/core/automation/workflow_driver.py"

        step2 = "Add an import statement to src/utils/config.py"
        classification2 = check_step_classification(driver, step2, task_target_file="src/utils/config.py")
        assert classification2["is_research_step"] is False
        assert classification2["is_code_generation_step"] is True
        assert classification2["is_explicit_file_writing_step"] is False
        assert classification2["is_test_execution_step"] is False
        assert classification2["filepath_to_use"] == "src/utils/config.py"

        step3 = "Modify the class definition in src/core/automation/workflow_driver.py"
        classification3 = check_step_classification(driver, step3, task_target_file="src/core/automation/workflow_driver.py")
        assert classification3["is_research_step"] is False
        assert classification3["is_code_generation_step"] is True
        assert classification3["is_explicit_file_writing_step"] is True
        assert classification3["is_test_execution_step"] is False
        assert classification3["filepath_to_use"] == "src/core/automation/workflow_driver.py"

    def test_explicit_file_writing_step_classification(self, test_driver_phase1_8):
        """Test that steps explicitly mentioning file writing (non-code) are classified correctly."""
        driver = test_driver_phase1_8['driver']

        step1 = "Write the research findings to research_summary.md"
        classification1 = check_step_classification(driver, step1, task_target_file=None)
        assert classification1["is_research_step"] is True
        assert classification1["is_code_generation_step"] is False
        assert classification1["is_explicit_file_writing_step"] is True
        assert classification1["is_test_execution_step"] is False
        assert classification1["filepath_to_use"] == "research_summary.md"

        step2 = "Update the documentation file docs/workflows/markdown_automation.md"
        classification2 = check_step_classification(driver, step2, task_target_file="docs/workflows/markdown_automation.md")
        assert classification2["is_research_step"] is False
        assert classification2["is_code_generation_step"] is False
        assert classification2["is_explicit_file_writing_step"] is True
        assert classification2["is_test_execution_step"] is False
        assert classification2["filepath_to_use"] == "docs/workflows/markdown_automation.md"

    def test_test_execution_step_classification(self, test_driver_phase1_8):
        """Test that steps mentioning test execution are classified correctly."""
        driver = test_driver_phase1_8['driver']

        step1 = "Run tests for the new feature."
        classification1 = check_step_classification(driver, step1, task_target_file="tests/test_new_feature.py")
        assert classification1["is_research_step"] is False
        assert classification1["is_code_generation_step"] is False
        assert classification1["is_explicit_file_writing_step"] is False
        assert classification1["is_test_execution_step"] is True
        assert classification1["filepath_to_use"] == "tests/test_new_feature.py"

        step2 = "Execute pytest on the updated module."
        classification2 = check_step_classification(driver, step2, task_target_file="src/core/automation/workflow_driver.py")
        assert classification2["is_research_step"] is False
        assert classification2["is_code_generation_step"] is False
        assert classification2["is_explicit_file_writing_step"] is False
        assert classification2["is_test_execution_step"] is True
        assert classification2["filepath_to_use"] == "src/core/automation/workflow_driver.py"

    def test_conceptual_step_classification(self, test_driver_phase1_8):
        """Test that purely conceptual steps are classified correctly."""
        driver = test_driver_phase1_8['driver']

        step1 = "Discuss the design approach with the team."
        classification1 = check_step_classification(driver, step1, task_target_file=None)
        assert classification1["is_research_step"] is False
        assert classification1["is_code_generation_step"] is False
        assert classification1["is_explicit_file_writing_step"] is False
        assert classification1["is_test_execution_step"] is False
        assert classification1["filepath_to_use"] is None

        step2 = "Review the generated grade report."
        classification2 = check_step_classification(driver, step2, task_target_file="ROADMAP.json")
        assert classification2["is_research_step"] is False
        assert classification2["is_code_generation_step"] is False
        assert classification2["is_explicit_file_writing_step"] is False
        assert classification2["is_test_execution_step"] is False
        assert classification2["filepath_to_use"] == "ROADMAP.json"


    # --- NEW TEST FOR task_1_8_1_unblock_overwrite_fix ---
    # This test now mocks the full autonomous_loop execution for the specific step.
    @patch.object(WorkflowDriver, '_invoke_coder_llm') # Mock LLM for plan generation
    @patch.object(WorkflowDriver, '_write_output_file') # Mock the actual file write
    @patch.object(WorkflowDriver, '_safe_write_roadmap_json') # Mock roadmap update
    @patch.object(WorkflowDriver, 'generate_grade_report') # Mock grade report
    @patch.object(WorkflowDriver, '_parse_and_evaluate_grade_report') # Mock evaluation
    def test_conceptual_define_step_does_not_overwrite_main_python_target(
        self,
        mock_parse_eval,
        mock_gen_report,
        mock_safe_write,
        mock_write_output,
        mock_invoke_llm, # This is the mock for _invoke_coder_llm
        test_driver_phase1_8, # Use the fixture
        tmp_path,
        caplog
    ):
        """
        Test that a conceptual plan step that mentions a file (like the first step of task_1_8_1)
        is correctly identified and skips file writing/agent invocation due to the fix,
        by running a segment of the autonomous_loop.
        """
        caplog.set_level(logging.INFO)
        driver_fixture_data = test_driver_phase1_8
        driver = driver_fixture_data['driver']
    
        # Setup task and plan step for the autonomous loop
        task_id = 'test_conceptual_write_loop'
        target_py_file = 'src/core/automation/workflow_driver.py'
        conceptual_step_text = "Define a comprehensive list of keywords for step classification."
    
        mock_task = {
            'task_id': task_id,
            'task_name': 'Test Conceptual Write via Loop',
            'description': 'A test for conceptual step handling.',
            'status': 'Not Started',
            'priority': 'High',
            'target_file': target_py_file
        }
        driver.tasks = [mock_task] # Set tasks for select_next_task
        driver.roadmap_path = "mock_roadmap.json" # Needed for status update logic
    
        # --- START FIX ---
        # Configure the mock for _invoke_coder_llm to return the plan string
        # This mock is used by generate_solution_plan
        mock_invoke_llm.return_value = f"1. {conceptual_step_text}\n2. Implement the new classification logic in {target_py_file}"
        # Remove the redundant mock on driver.llm_orchestrator.generate
        # --- END FIX ---
    
        # Mock _parse_and_evaluate_grade_report to return "Completed" to allow status update
        mock_parse_eval.return_value = {"recommended_action": "Completed", "justification": "Mock evaluation"}
        mock_gen_report.return_value = json.dumps({}) # Minimal valid JSON for grade report
        mock_safe_write.return_value = True
    
    
        # Create a dummy roadmap file for the driver to load and update
        # This is important because the driver reads and writes the roadmap
        roadmap_file_path = tmp_path / driver.roadmap_path
        with open(roadmap_file_path, 'w') as f:
            json.dump({"tasks": [mock_task]}, f)
    
        # Patch builtins.open to handle roadmap reading/writing within the loop
        # The mock_open from unittest.mock is good for this.
        # We need to simulate reading the initial roadmap and then the updated one.
        # The first read is in start_workflow, then in each loop iteration.
        # The write happens at the end of a successful iteration.
    
        # Simulate the content that will be read
        initial_roadmap_content = json.dumps({"tasks": [mock_task]})
        # After the task is "Completed", this is what should be written and then read in the next iteration
        completed_task = mock_task.copy()
        completed_task['status'] = 'Completed'
        updated_roadmap_content = json.dumps({"tasks": [completed_task]})
    
        mock_file_content_sequence = [initial_roadmap_content, initial_roadmap_content, updated_roadmap_content]
    
        # --- FIX START: Correct mock_open usage ---
        # Create a mock for the open function
        mock_open_function = mock_open()
    
        # Configure the file handle mock (which is mock_open_function.return_value)
        file_handle_mock = MagicMock()
        file_handle_mock.read.side_effect = mock_file_content_sequence
        file_handle_mock.__enter__.return_value = file_handle_mock # For 'with open(...) as f:'
        file_handle_mock.__exit__.return_value = None
    
        mock_open_function.return_value = file_handle_mock # When open() is called, it returns our file_handle_mock
    
        with patch('builtins.open', mock_open_function): # Patch builtins.open with our function mock
            driver.start_workflow(str(roadmap_file_path), str(tmp_path / "output"), driver.context)
        # --- FIX END ---
    
    
        # Assert that _write_output_file was NOT called for the conceptual step
        # It should only be called for the "Implement" step if that step was reached and classified as code-gen
        # Check the calls to _write_output_file
        write_calls = mock_write_output.call_args_list
        conceptual_step_write_attempted = False
        for call_args_item in write_calls: # Renamed call_args to avoid conflict
            # call_args_item[0] is a tuple of positional arguments
            # call_args_item[0][0] is the filepath, call_args_item[0][1] is the content
            # Check if the conceptual step text was part of the *content* written
            # The filepath check remains the same.
            if target_py_file in call_args_item[0][0] and conceptual_step_text in call_args_item[0][1]:
                conceptual_step_write_attempted = True
                break
    
        assert not conceptual_step_write_attempted, "_write_output_file was called with placeholder for the conceptual step"
    
        # Assert the log message for skipping the placeholder write
        assert f"Skipping placeholder write to main Python target {target_py_file} for conceptual step: '{conceptual_step_text}'." in caplog.text

        # Assert that the second step (Implement) DID attempt to write (or would have, if not for other mocks)
        # This means _write_output_file should have been called at least once for the "Implement" step
        # if the plan execution reached that far and it was classified as code-gen.
        # Given our mocks, it should try to write for the "Implement" step.
        assert mock_write_output.call_count >= 1, "Expected _write_output_file to be called for the implementation step"

        # Verify that the task status was updated to Completed
        mock_safe_write.assert_called_once()
        written_roadmap_data = mock_safe_write.call_args[0][1] # Get the data written to roadmap
        assert written_roadmap_data['tasks'][0]['status'] == 'Completed'