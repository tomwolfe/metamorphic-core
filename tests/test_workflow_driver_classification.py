# tests/test_workflow_driver_classification.py
import pytest
from src.core.automation.workflow_driver import WorkflowDriver, Context
from unittest.mock import patch

@pytest.fixture
def driver_for_classification(tmp_path, mocker):
    """Fixture to create a WorkflowDriver instance for testing classification."""
    context = Context(str(tmp_path))
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'):
        driver = WorkflowDriver(context)
        yield driver

@pytest.mark.parametrize("description, expected_is_code_gen", [
    # Test cases for the newly added keywords
    ("insert the while loop structure", True),
    ("add a retry counter variable", True),
    ("create a code block with a pass statement", True),
    ("insert a new snippet of code", True),
    # Regression test for previously working keywords
    ("implement the main function", True),
    ("add a new import for os", True),
    ("modify the existing class", True),
    # Test cases that should NOT be code generation
    ("research the best way to implement a loop", False),
    ("analyze the structure of the file", False),
])
def test_classify_step_preliminary_with_new_keywords(driver_for_classification, description, expected_is_code_gen):
    """
    Tests that _classify_step_preliminary correctly identifies code generation steps
    with the newly added keywords and avoids false positives.
    """
    driver = driver_for_classification
    prelim_flags = driver._classify_step_preliminary(description, "src/some_file.py")
    assert prelim_flags["is_code_generation_step_prelim"] == expected_is_code_gen
