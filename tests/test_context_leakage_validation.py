# tests/unit/test_context_leakage_validation.py
import pytest
import unittest
from unittest.mock import MagicMock, patch

# Import necessary components from workflow_driver
from src.core.automation.workflow_driver import WorkflowDriver, Context

# Import constants from the centralized constants file
from src.core.constants import CONTEXT_LEAKAGE_INDICATORS

# Fixture for a WorkflowDriver instance with mocked dependencies for context leakage tests.
@pytest.fixture
def driver_for_context_leakage_tests(tmp_path, mocker):
    context = Context(str(tmp_path))
    mocker.patch.object(WorkflowDriver, '_load_default_policy') # Mock policy loading
    with patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'), \
         patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'):
        driver = WorkflowDriver(context)
    return driver

class TestContextLeakageValidation:
    """Test suite for the _validate_for_context_leakage method."""

    # Note: This test uses a pytest fixture (`driver_for_context_leakage_tests`)
    # which is passed as an argument. This is a common pattern when mixing
    # unittest.TestCase with pytest fixtures.
    @pytest.mark.parametrize("snippet, expected", [
        ("def func():\n    # ```python\n    pass", False),
        ("As an AI language model, I suggest this code.", False),
        ("I am a large language model, and here is the code.", False),
        ("I am an AI assistant, here's the fix.", False),
        ("This is a clean snippet of code.", True),
        ("def another_func():\n    return True", True),
        ("", True),
    ])
    def test_validate_for_context_leakage(self, driver_for_context_leakage_tests, snippet, expected):
        """
        Tests the _validate_for_context_leakage method with various snippets.
        """
        driver = driver_for_context_leakage_tests
        # Call the original method directly from the class, bypassing the instance mock from the fixture.
        result = WorkflowDriver._validate_for_context_leakage(driver, snippet)
        assert result == expected