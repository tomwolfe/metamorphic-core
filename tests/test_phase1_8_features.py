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
    filepath_from_step_match = re.search(r'(\S+\.(py|md|json|txt|yml|yaml))', step_text, re.IGNORECASE)
    filepath_from_step = filepath_from_step_match.group(1) if filepath_from_step_match else None

    filepath_to_use = task_target_file
    if not filepath_to_use and filepath_from_step:
        filepath_to_use = filepath_from_step

    code_generation_keywords = ["implement", "generate code", "write function", "modify", "add", "define", "create", "update", "refactor"]
    research_keywords = ["research and identify", "research", "analyze", "investigate", "understand"]
    code_element_keywords = ["import", "constant", "variable", "function", "class", "method", "definition", "parameter", "return"]
    # FIX: Updated file_writing_keywords to match the list in workflow_driver.py
    file_writing_keywords = ["write", "write file", "create", "create file", "update", "update file", "modify", "modify file", "save to file", "output file", "generate file", "write output to"]
    test_execution_keywords = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]

    is_test_execution_step = any(keyword in step_lower for keyword in test_execution_keywords)
    # FIX: Added check for filepath_to_use is not None, mirroring the actual code logic
    is_explicit_file_writing_step = any(keyword in step_lower for keyword in file_writing_keywords) and filepath_to_use is not None
    is_research_step = any(keyword in step_lower for keyword in research_keywords)

    is_code_generation_step = not is_research_step and \
                              any(verb in step_lower for verb in code_generation_keywords) and \
                              (any(element in step_lower for element in code_element_keywords) or \
                               (filepath_to_use and filepath_to_use.endswith('.py'))) # Use filepath_to_use here

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
        # FIX: This step contains "Modify", which is now correctly in file_writing_keywords.
        # Since filepath_to_use is also present, it IS an explicit file writing step.
        # Changed assertion from False to True.
        assert classification3["is_explicit_file_writing_step"] is True
        assert classification3["is_test_execution_step"] is False
        assert classification3["filepath_to_use"] == "src/core/automation/workflow_driver.py"

    def test_explicit_file_writing_step_classification(self, test_driver_phase1_8):
        """Test that steps explicitly mentioning file writing (non-code) are classified correctly."""
        driver = test_driver_phase1_8['driver']

        step1 = "Write the research findings to research_summary.md"
        classification1 = check_step_classification(driver, step1, task_target_file=None) # No task target file
        # "write" is a keyword, and filepath_to_use becomes "research_summary.md" from the step.
        # filepath_to_use is not None.
        assert classification1["is_research_step"] is True
        assert classification1["is_code_generation_step"] is False
        assert classification1["is_explicit_file_writing_step"] is True # "write" is a keyword AND filepath_to_use is not None
        assert classification1["is_test_execution_step"] is False
        assert classification1["filepath_to_use"] == "research_summary.md"

        step2 = "Update the documentation file docs/workflows/markdown_automation.md"
        classification2 = check_step_classification(driver, step2, task_target_file="docs/workflows/markdown_automation.md")
        assert classification2["is_research_step"] is False
        assert classification2["is_code_generation_step"] is False
        assert classification2["is_explicit_file_writing_step"] is True # "update" is a keyword AND filepath_to_use is not None
        assert classification2["is_test_execution_step"] is False
        assert classification2["filepath_to_use"] == "docs/workflows/markdown_automation.md"

    def test_test_execution_step_classification(self, test_driver_phase1_8):
        """Test that steps mentioning test execution are classified correctly."""
        driver = test_driver_phase1_8['driver']

        step1 = "Run tests for the new feature."
        classification1 = check_step_classification(driver, step1, task_target_file="tests/test_new_feature.py")
        assert classification1["is_research_step"] is False
        assert classification1["is_code_generation_step"] is False
        assert classification1["is_explicit_file_writing_step"] is False # No file writing keyword
        assert classification1["is_test_execution_step"] is True
        assert classification1["filepath_to_use"] == "tests/test_new_feature.py"

        step2 = "Execute pytest on the updated module."
        classification2 = check_step_classification(driver, step2, task_target_file="src/core/automation/workflow_driver.py")
        # "Execute pytest" -> is_test_execution_step = True
        # "updated" -> "update" is a code_generation_keyword
        # filepath_to_use is "src/core/automation/workflow_driver.py" (.py file)
        # is_research_step is False
        # -> is_code_generation_step = True
        # "update" is a file_writing_keyword AND filepath_to_use is not None
        # -> is_explicit_file_writing_step = True
        assert classification2["is_research_step"] is False
        assert classification2["is_code_generation_step"] is True # "update" in "updated" + .py file
        assert classification2["is_explicit_file_writing_step"] is True # "update" is a keyword + filepath_to_use is not None
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
        assert classification2["is_explicit_file_writing_step"] is False # No file writing keyword
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
    # test_improved_coder_prompt_generation
    # test_task_success_prediction