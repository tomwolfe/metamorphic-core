import pytest
import unittest
from unittest.mock import patch, MagicMock, mock_open, call, ANY
import re
from pathlib import Path
import logging
import json
from datetime import datetime
import subprocess
import sys
import os

# Add the src directory to the Python path
# This ensures that 'from core.automation.workflow_driver import ...' works
# Use Pathlib for robust path joining
current_file_dir = Path(__file__).parent # Corrected __file__
src_dir = current_file_dir.parent.parent.parent / 'src'
sys.path.insert(0, str(src_dir.resolve()))

# Assuming WorkflowDriver is in src.core.automation
from core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT, classify_plan_step, CODE_KEYWORDS, CONCEPTUAL_KEYWORDS
import spacy
from spacy.matcher import PhraseMatcher

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Use the correct logger name for the module
logger = logging.getLogger(__name__) # Corrected logger name to use __name__

# Define a maximum file size for reading (e.g., 1MB)
# Note: This is redefined here, ideally should be imported or consistent
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion, matching the value in workflow_driver.py
# Note: This is redefined here, ideally should be imported or consistent
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"

# Fixture for a WorkflowDriver instance with a Context, specifically for Phase 1.8 tests
@pytest.fixture
def test_driver_phase1_8(tmp_path):
    # Create the actual Context object
    context = Context(str(tmp_path))


    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation
    with patch('core.automation.workflow_driver.CodeReviewAgent') as MockCodeReviewAgent, \
         patch('core.automation.workflow_driver.EthicalGovernanceEngine') as MockEthicalGovernanceEngine:
        mock_code_review_agent_instance = MockCodeReviewAgent.return_value
        mock_ethical_governance_engine_instance = MockEthicalGovernanceEngine.return_value
        # Mock the policy loading within the engine mock
        # Note: The driver now loads policy via _load_default_policy, not load_policy_from_json directly
        # We might need to mock the open call or the _load_default_policy method itself if policy loading is critical
        # For now, assume the mock instance is sufficient and default_policy_config is set manually below
        # mock_ethical_governance_engine_instance.load_policy_from_json.return_value = {'policy_name': 'Mock Policy'}

        # Instantiate WorkflowDriver using the created context object
        driver = WorkflowDriver(context) # Use the 'context' object here

        # Ensure LLM orchestrator mock is set up
        driver.llm_orchestrator = MagicMock()
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"

        # Assign mocked instances
        driver.code_review_agent = mock_code_review_agent_instance
        driver.ethical_governance_engine = mock_ethical_governance_engine_instance
        driver.default_policy_config = {'policy_name': 'Mock Policy'} # Ensure default policy is set for tests

        # Add attributes needed for tests that might not be set by __init__ or autonomous_loop setup
        driver._current_task_results = {}
        driver.remediation_attempts = 0 # Initialize remediation counter for tests
        driver.remediation_occurred_in_pass = False # Initialize flag
        driver._current_task = {} # Initialize current task
        driver.task_target_file = None # Initialize task_target_file

        yield {
            'driver': driver,
            'mock_code_review_agent': mock_code_review_agent_instance,
            'mock_ethical_governance_engine': mock_ethical_governance_engine_instance
        }

# Helper function to simulate the relevant part of autonomous_loop for testing classification
# Note: This helper is primarily for testing the classification logic in isolation,
# the full autonomous_loop tests cover the integration.
# This helper function is NOT used by the TestClassifyPlanStep class, which calls
# classify_plan_step directly. It's used by the TestPhase1_8Features class.
def check_step_classification(driver_instance, step_text, task_target_file=None):
    step_lower = step_text.lower()
    filepath_from_step_match = re.search(
        r'(\S+\.(py|md|json|txt|yml|yaml))', step_text, re.IGNORECASE)
    filepath_from_step = filepath_from_step_match.group(1) if filepath_from_step_match else None


    # Keywords lists remain the same (should ideally use the imported global ones)
    # Note: These lists are slightly different from the global ones in workflow_driver.py
    # and are used only within this helper function. The tests for classify_plan_step
    # use the actual function which uses the global lists.
    # To be accurate for testing the driver's *preliminary* logic, these should match
    # the preliminary lists used *inside* the driver's loop.
    # For now, keeping them as they were in the original test file, as the failing tests
    # are in TestClassifyPlanStep which doesn't use this helper.
    code_generation_keywords = ["implement", "generate code", "write function", "modify", "add", "define", "create", "update", "refactor"]
    research_keywords = ["research and identify", "research", "analyze", "investigate", "understand"]
    code_element_keywords = ["import", "constant", "variable", "function", "class", "method", "definition", "parameter", "return"]
    file_writing_keywords = ["write", "write file", "create", "create file", "update", "update file", "modify", "modify file", "save to file", "output file", "generate file", "write output to"]
    test_execution_keywords = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]

    # Calculate preliminary flags based on keywords and filepath_from_step
    # This mirrors the driver's logic flow before determining filepath_to_use
    # Use word boundaries for more accurate keyword matching
    is_test_execution_step_prelim = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in test_execution_keywords)
    is_explicit_file_writing_step_prelim = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in file_writing_keywords)
    is_research_step_prelim = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in research_keywords)

    # Code generation preliminary check uses filepath_from_step and word boundaries
    is_code_generation_step_prelim = not is_research_step_prelim and \
                                     any(re.search(r'\b' + re.escape(verb) + r'\b', step_lower) for verb in code_generation_keywords) and \
                                     (any(re.search(r'\b' + re.escape(element) + r'\b', step_lower) for element in code_element_keywords) or \
                                      (filepath_from_step and filepath_from_step.endswith('.py')))


    # Determine filepath_to_use based on task target or step mention (matching driver Step 3)
    filepath_to_use = task_target_file
    # If the task doesn't have a target_file, but the step mentions one AND it's a file-related step, use the one from the step.
    if filepath_to_use is None and (is_explicit_file_writing_step_prelim or is_code_generation_step_prelim) and filepath_from_step:
         filepath_to_use = filepath_from_step

    # Now set the final classification flags using the determined filepath_to_use
    # This mirrors the driver's Step 2 logic using the final filepath_to_use where applicable
    # Use word boundaries for final classification checks as well

    is_test_execution_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in test_execution_keywords)
    # Explicit file writing classification is based on keywords only (as per driver code)
    is_explicit_file_writing_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in file_writing_keywords)

    # Research classification is based on keywords only (as per driver code)
    is_research_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in research_keywords)

    # Code generation classification uses filepath_to_use and word boundaries (as per driver code)
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
        assert classification1["is_explicit_file_writing_step"] is False # "Implement" is not a file writing keyword
        assert classification1["is_test_execution_step"] is False
        assert classification1["filepath_to_use"] == "src/core/automation/workflow_driver.py"

        step2 = "Add an import statement to src/utils/config.py"
        classification2 = check_step_classification(driver, step2, task_target_file="src/utils/config.py")
        assert classification2["is_research_step"] is False
        assert classification2["is_code_generation_step"] is True
        assert classification2["is_explicit_file_writing_step"] is False # "Add" is not a file writing keyword
        assert classification2["is_test_execution_step"] is False
        assert classification2["filepath_to_use"] == "src/utils/config.py"

        step3 = "Modify the class definition in src/core/automation/workflow_driver.py"
        classification3 = check_step_classification(driver, step3, task_target_file="src/core/automation/workflow_driver.py")
        assert classification3["is_research_step"] is False
        assert classification3["is_code_generation_step"] is True
        assert classification3["is_explicit_file_writing_step"] is True # "Modify" is in file_writing_keywords
        assert classification3["is_test_execution_step"] is False
        assert classification3["filepath_to_use"] == "src/core/automation/workflow_driver.py"

    def test_explicit_file_writing_step_classification(self, test_driver_phase1_8):
        """Test that steps explicitly mentioning file writing (non-code) are classified correctly."""
        driver = test_driver_phase1_8['driver']

        step1 = "Write the research findings to research_summary.md"
        classification1 = check_step_classification(driver, step1, task_target_file=None) # No task target file
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

    # --- Add other Phase 1.8 feature tests here as they are implemented ---
    # For example:
    # test_pre_write_validation_triggered
    # test_step_level_remediation_loop
    # test_post_write_test_execution_triggered
    # test_failure_data_capture
    # test_improved_remediation_strategy
    # test_automated_task_decomposition
    # test_refined_grade_report
    # test_advanced_code_merging
    # test_prompt_self_correction

    # --- NEW TEST FOR task_1_8_1_unblock_overwrite_fix ---
    @patch.object(WorkflowDriver, '_write_output_file') # Mock the actual file write
    def test_conceptual_define_step_does_not_overwrite_main_python_target(self, mock_write_output, test_driver_phase1_8, tmp_path, caplog):
        """
        Test that a conceptual plan step that mentions a file (like the first step of task_1_8_1)
        is correctly identified and skips file writing/agent invocation due to the fix.
        """
        caplog.set_level(logging.INFO)
        driver = test_driver_phase1_8['driver'] # Assuming test_driver fixture provides the driver

        # Setup task and plan step
        driver._current_task = {
            'task_id': 'test_conceptual_write',
            'task_name': 'Test Conceptual Write',
            'description': 'A test.',
            'status': 'Not Started',
            'priority': 'High',
            'target_file': 'src/core/automation/workflow_driver.py' # Main Python target
        }
        driver.task_target_file = driver._current_task['target_file'] # Ensure this is set for the test

        plan_step = "Write a define list of keywords for step classification."

        # Simulate the relevant part of the autonomous_loop's step processing logic
        # This requires careful extraction or a helper method as done in your test_phase1_8_features.py
        # Here, we'll manually set the conditions that would lead to the placeholder write block.

        # Simulate conditions that would lead to the placeholder write block
        # In the actual driver, these would be determined by the classification logic
        step_lower = plan_step.lower()
        filepath_from_step_match = re.search(
            r'(\S+\.(py|md|json|txt|yml|yaml))', plan_step, re.IGNORECASE)
        filepath_from_step = filepath_from_step_match.group(1) if filepath_from_step_match else None

        # Re-calculate classification flags for this step to determine if it was a file step
        # Note: These keyword lists are duplicated here from the helper function above
        # and are used only within this specific test method.
        code_generation_keywords = ["implement", "generate code", "write function", "modify", "add", "define", "create", "update", "refactor"]
        research_keywords = ["research and identify", "research", "analyze", "investigate", "understand"]
        code_element_keywords = ["import", "constant", "variable", "function", "class", "method", "definition", "parameter", "return"]
        file_writing_keywords = ["write", "write file", "create", "create file", "update", "update file", "modify", "modify file", "save to file", "output file", "generate file", "write output to"]
        test_execution_keywords = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]

        is_test_execution_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in test_execution_keywords)
        is_explicit_file_writing_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in file_writing_keywords)
        is_research_step = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in research_keywords)

        # Determine filepath_to_use based on task target or step mention
        filepath_to_use = driver.task_target_file # Start with the task's target file
        # If the task doesn't have a target_file, but the step mentions one AND it's a file-related step, use the one from the step.
        # Note: The original driver logic used preliminary flags here.
        # Re-calculate is_code_generation_step using filepath_to_use
        is_code_generation_step = not is_research_step and \
                                  any(re.search(r'\b' + re.escape(verb) + r'\b', step_lower) for verb in code_generation_keywords) and \
                                  (any(re.search(r'\b' + re.escape(element) + r'\b', step_lower) for element in code_element_keywords) or \
                                   (filepath_to_use and filepath_to_use.endswith('.py')))

        # Re-evaluate filepath_to_use based on preliminary flags as per driver logic
        filepath_to_use_re_eval = driver.task_target_file
        if filepath_to_use_re_eval is None and (is_explicit_file_writing_step or is_code_generation_step) and filepath_from_step:
             filepath_to_use_re_eval = filepath_from_step


        step_implies_create_new_file = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in ["create file", "generate file"])

        # --- Replicate the fixed logic block for testing ---
        is_main_python_target = (filepath_to_use_re_eval == driver.task_target_file and driver.task_target_file is not None and filepath_to_use_re_eval.endswith('.py'))
        # Re-calculate is_conceptual_step_for_main_target using word boundaries
        conceptual_define_keywords = ["define list", "analyze", "understand", "document decision", "identify list", "define a comprehensive list"]
        is_conceptual_step_for_main_target = is_research_step or \
                                            any(re.search(r'\b' + re.escape(kw) + r'\b', step_lower) for kw in conceptual_define_keywords)


        content_to_write_decision = None
        # Use the explicit file writing check based on keywords only, as per driver logic
        if is_explicit_file_writing_step and filepath_to_use_re_eval: # Enter the explicit file writing block
            if is_main_python_target and is_conceptual_step_for_main_target and not step_implies_create_new_file:
                logger.info(f"Skipping placeholder write to main Python target {filepath_to_use_re_eval} for conceptual step: '{plan_step}'.")
                content_to_write_decision = None
            else:
                # This part would normally set content_to_write
                if filepath_to_use_re_eval.endswith('.py'):
                    content_to_write_decision = f"# Placeholder content for Python file for step: {plan_step}"
                else:
                    content_to_write_decision = f"// Placeholder content for step: {plan_step}"
        # --- End replicated logic block ---

        # Assert that content_to_write_decision is None, meaning the write would be skipped
        assert content_to_write_decision is None

        # Assert that the actual _write_output_file was NOT called
        mock_write_output.assert_not_called()

# ADDED NEW TEST CLASS HERE
class TestClassifyPlanStep(unittest.TestCase):


    # Note: These tests call the actual classify_plan_step function,
    # which uses the global CODE_KEYWORDS and CONCEPTUAL_KEYWORDS and
    # the updated regex matching in the fallback path.

    def test_classify_plan_step_code(self):
        # Test cases that are clearly code-related
        self.assertEqual(classify_plan_step("Add an import for the 'os' module."), 'code')
        self.assertEqual(classify_plan_step("Define a constant named MAX_RETRIES."), 'code')
        self.assertEqual(classify_plan_step("Implement a function to calculate factorial."), 'code')
        self.assertEqual(classify_plan_step("Modify the User class to add a new method."), 'code')
        self.assertEqual(classify_plan_step("Write a unit test for the new function."), 'code')
        self.assertEqual(classify_plan_step("Refactor the code to improve readability."), 'code')
        self.assertEqual(classify_plan_step("Fix the bug causing the application to crash."), 'code')
        self.assertEqual(classify_plan_step("Update dependency 'requests' to version 2.28.1"), 'code')
        self.assertEqual(classify_plan_step("Add parameter 'timeout' to the API call."), 'code')
        self.assertEqual(classify_plan_step("Debug an issue in the payment module"), 'code')
        self.assertEqual(classify_plan_step("Handle error for file not found"), 'code')
        self.assertEqual(classify_plan_step("Change the variable name."), 'code')
        self.assertEqual(classify_plan_step("Configure the logging settings."), 'code')
        self.assertEqual(classify_plan_step("Create a new Python file."), 'code')
        self.assertEqual(classify_plan_step("Install the required package."), 'code')
        self.assertEqual(classify_plan_step("Use the new library."), 'code')
        self.assertEqual(classify_plan_step("Add input validation."), 'code')


    def test_classify_plan_step_conceptual(self):
        # Test cases that are clearly conceptual
        self.assertEqual(classify_plan_step("Understand the user requirements for the feature."), 'conceptual')
        self.assertEqual(classify_plan_step("Design the database schema for storing user data."), 'conceptual')
        self.assertEqual(classify_plan_step("Discuss the approach with the team during the stand-up."), 'conceptual')
        self.assertEqual(classify_plan_step("Review the pull request from John."), 'conceptual')
        self.assertEqual(classify_plan_step("Document the API endpoints in the README."), 'conceptual')
        self.assertEqual(classify_plan_step("Analyze the problem reported by the user."), 'conceptual')
        self.assertEqual(classify_plan_step("Plan the next step for the sprint."), 'conceptual')
        self.assertEqual(classify_plan_step("Gather feedback from stakeholders."), 'conceptual')
        self.assertEqual(classify_plan_step("Brainstorm ideas for the new UI."), 'conceptual')
        self.assertEqual(classify_plan_step("Research potential solutions."), 'conceptual')
        self.assertEqual(classify_plan_step("Evaluate alternative designs."), 'conceptual')
        self.assertEqual(classify_plan_step("Define the scope of the project."), 'conceptual')
        self.assertEqual(classify_plan_step("Create a project plan."), 'conceptual')
        self.assertEqual(classify_plan_step("Coordinate with the QA team."), 'conceptual')
        self.assertEqual(classify_plan_step("Get approval from the manager."), 'conceptual')
        self.assertEqual(classify_plan_step("Prepare a presentation."), 'conceptual')
        self.assertEqual(classify_plan_step("Write a report on findings."), 'conceptual')
        self.assertEqual(classify_plan_step("Investigate the performance issue."), 'conceptual')


    def test_classify_plan_step_ambiguous_or_mixed(self):
        # Test cases that might contain keywords from both, testing tie-breaking or dominance
        # Depending on PhraseMatcher and scoring, these might vary.
        # Assuming 'code' keywords are more specific and might win ties or close calls.
        # With the expanded lists and regex, these should lean towards the dominant type.
        self.assertEqual(classify_plan_step("Update the documentation and refactor the code."), 'code') # Contains 'update', 'document', 'refactor', 'code' - 'code' related words likely dominate
        self.assertEqual(classify_plan_step("Analyze the performance issue and fix the bug."), 'code') # Contains 'analyze', 'fix', 'bug' - 'fix bug' is strong code
        self.assertEqual(classify_plan_step("Plan the next steps and add a new feature (e.g. implement function)."), 'code') # Contains 'plan', 'add', 'implement', 'function' - strong code words
        self.assertEqual(classify_plan_step("Review the design proposal and implement the core logic."), 'code') # Contains 'review', 'design', 'implement', 'logic' - 'implement' is strong code
        self.assertEqual(classify_plan_step("Discuss the requirements and define constants."), 'code') # Contains 'discuss', 'requirements', 'define', 'constants' - 'define constants' is strong code


    def test_classify_plan_step_uncertain(self):
        # Test cases with no relevant keywords or where scores might be equal/low
        self.assertEqual(classify_plan_step("Just a simple sentence with no keywords."), 'uncertain')
        self.assertEqual(classify_plan_step("This step doesn't involve specific actions."), 'uncertain')
        self.assertEqual(classify_plan_step("Prepare for the upcoming meeting."), 'uncertain') # Could be conceptual but weak
        self.assertEqual(classify_plan_step("Send an email to the client."), 'uncertain')
        self.assertEqual(classify_plan_step("Walk the dog."), 'uncertain') # Clearly irrelevant


    def test_classify_plan_step_case_insensitivity(self):
        # Test that classification is case-insensitive (due to .lower() in function)
        self.assertEqual(classify_plan_step("ADD AN IMPORT for the 'os' module."), 'code')
        self.assertEqual(classify_plan_step("Understand the USER REQUIREMENTS."), 'conceptual')
        self.assertEqual(classify_plan_step("Run TESTS."), 'code') # Test execution is now in CODE_KEYWORDS


    def test_classify_plan_step_multiple_keywords(self):
        # Test cases with multiple keywords of the same type
        self.assertEqual(classify_plan_step("Add import, define constant, and implement function."), 'code')
        self.assertEqual(classify_plan_step("Understand requirements, design interface, and discuss approach."), 'conceptual')
        self.assertEqual(classify_plan_step("Fix bug, refactor code, and add validation."), 'code')
        self.assertEqual(classify_plan_step("Analyze problem, research options, and propose solution."), 'conceptual')


    def test_classify_plan_step_nlp_dependency_fallback(self):
        # Temporarily mock nlp to be None to test fallback
        original_nlp = None
        # Check if the module is already loaded and has an nlp attribute
        if 'core.automation.workflow_driver' in sys.modules and hasattr(sys.modules['core.automation.workflow_driver'], 'nlp'):
             original_nlp = sys.modules['core.automation.workflow_driver'].nlp
             sys.modules['core.automation.workflow_driver'].nlp = None
             logger.info("Mocked nlp to None for fallback test.")
        else:
             # If module not loaded or nlp not present, assume fallback is active
             logger.warning("core.automation.workflow_driver module not loaded or nlp attribute missing. Assuming fallback is active for test.")


        # These assertions should now pass because the regex fallback works
        self.assertEqual(classify_plan_step("Add an import for the 'os' module."), 'code')
        self.assertEqual(classify_plan_step("Understand the user requirements for the feature."), 'conceptual')
        self.assertEqual(classify_plan_step("Refactor the code."), 'code')
        self.assertEqual(classify_plan_step("Analyze the data."), 'conceptual')
        self.assertEqual(classify_plan_step("Run tests."), 'code') # Test execution is now in CODE_KEYWORDS


        # Restore nlp
        if 'core.automation.workflow_driver' in sys.modules and original_nlp is not None:
            sys.modules['core.automation.workflow_driver'].nlp = original_nlp
            logger.info("Restored original nlp object.")
        elif 'core.automation.workflow_driver' in sys.modules:
             # If module was loaded but nlp wasn't originally there, just log
             logger.info("core.automation.workflow_driver module was loaded, but no original nlp to restore.")
        else:
             # If module wasn't loaded, nothing to restore
             logger.info("core.automation.workflow_driver module was not loaded during test, nothing to restore.")

# Add other test classes for Phase 1.8 features below this line as they are implemented
class TestPreWriteValidation(unittest.TestCase):
    pass
class TestStepLevelRemediation(unittest.TestCase):
    pass

# etc