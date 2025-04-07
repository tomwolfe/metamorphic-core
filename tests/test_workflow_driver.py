# tests/test_workflow_driver.py
import pytest
from unittest.mock import MagicMock
from src.core.automation.workflow_driver import WorkflowDriver
import unittest

class TestWorkflowDriverUnit(unittest.TestCase): # Convert to use unittest TestCase class
    def test_workflow_driver_execute_workflow(self): # Add self as the first argument
        mock_llm_orchestrator = MagicMock()
        mock_llm_orchestrator.generate.return_value = "Mock LLM Output"
        driver = WorkflowDriver(mock_llm_orchestrator)
        result = driver.execute_workflow("Test Task")
        self.assertEqual(result, "Mock LLM Output")
        mock_llm_orchestrator.generate.assert_called_once()
