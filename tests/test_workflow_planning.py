# tests/test_workflow_planning.py

import pytest
import html
from src.core.automation.workflow_driver import WorkflowDriver, Context
import logging
from unittest.mock import MagicMock, patch
import re

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_planning(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation as they are not needed for planning tests
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'):
        driver = WorkflowDriver(context)
        # Replace the real orchestrator with a mock
        driver.llm_orchestrator = MagicMock()
        # Default mock return for generate, can be overridden in tests
        driver.llm_orchestrator.generate.return_value = "Test response from LLM"
        yield driver

class TestWorkflowPlanning:

    # --- Tests for generate_solution_plan parsing ---
    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_parses_valid_list(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan correctly parses a valid numbered markdown list."""
        driver = test_driver_planning
        mock_llm_output = """
1.  First step.
2.  Second step.
3.  Third step.
"""
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == ["First step.", "Second step.", "Third step."]

    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_handles_whitespace(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan handles leading/trailing whitespace and blank lines."""
        driver = test_driver_planning
        mock_llm_output = """

    1.  Step one with whitespace.

2.  Step two.   \n
3.  Step three.

"""
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == ["Step one with whitespace.", "Step two.", "Step three."]

    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_handles_multiline_steps(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan correctly parses multi-line steps."""
        driver = test_driver_planning
        mock_llm_output = """
1.  First step that
    spans multiple lines.
2.  Second step.
"""
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == ["First step that spans multiple lines.", "Second step."]

    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_handles_non_list_output(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan handles LLM output that is not a numbered list."""
        driver = test_driver_planning
        mock_llm_output = "This is not a numbered list. Just some text."
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == [], "Should return an empty list if output is not a numbered list"

    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_handles_empty_output(self, mock_invoke_coder_llm, test_driver_planning, caplog):
        """Test generate_solution_plan handles empty string output from LLM."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_planning
        mock_llm_output = ""
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == [], "Should return an empty list for empty LLM output"
        assert "LLM returned empty response for plan generation" in caplog.text

    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_handles_none_output(self, mock_invoke_coder_llm, test_driver_planning, caplog):
        """Test generate_solution_plan handles None output from _invoke_coder_llm."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_planning
        mock_llm_output = None
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == [], "Should return an empty list for None LLM output"
        assert "LLM returned empty response for plan generation" in caplog.text

    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_sanitizes_markdown(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan sanitizes markdown formatting from steps."""
        driver = test_driver_planning
        mock_llm_output = """
1.  **Bold step**.
2.  _Italic step_.
3.  `Code step`.
"""
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == ["Bold step.", "Italic step.", "Code step."]

    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    def test_generate_solution_plan_preserves_html_chars(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan preserves HTML characters in steps."""
        driver = test_driver_planning
        mock_llm_output = """
1.  Step with <tag>.
2.  Step with & entity.
3.  Step with > and <.
"""
        mock_invoke_coder_llm.return_value = mock_llm_output
        mock_task = {'task_id': 'mock_task', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High', 'status': 'Not Started'}

        plan = driver.generate_solution_plan(mock_task)

        mock_invoke_coder_llm.assert_called_once()
        assert plan == ["Step with <tag>.", "Step with & entity.", "Step with > and <."]

    # --- Tests for generate_solution_plan prompt generation (New tests for the heuristic change) ---
    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="1. Step.")
    def test_generate_solution_plan_includes_target_file_context_task_name(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan includes target file context when 'WorkflowDriver' is in task name."""
        driver = test_driver_planning
        mock_task = {
            'task_id': 'mock_task',
            'task_name': 'Enhance the WorkflowDriver',
            'description': 'Implement a feature.',
            'priority': 'High', 'status': 'Not Started'
        }
        driver.generate_solution_plan(mock_task)
        called_prompt = mock_invoke_coder_llm.call_args[0][0]
        assert "The primary file being modified for this task is `src/core/automation/workflow_driver.py`." in called_prompt

    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="1. Step.")
    def test_generate_solution_plan_includes_target_file_context_description(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan includes target file context when 'workflow_driver.py' is in description."""
        driver = test_driver_planning
        mock_task = {
            'task_id': 'mock_task',
            'task_name': 'Implement a feature',
            'description': 'Modify the file src/core/automation/workflow_driver.py.',
            'priority': 'High', 'status': 'Not Started'
        }
        driver.generate_solution_plan(mock_task)
        called_prompt = mock_invoke_coder_llm.call_args[0][0]
        assert "The primary file being modified for this task is `src/core/automation/workflow_driver.py`." in called_prompt

    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="1. Step.")
    def test_generate_solution_plan_excludes_target_file_context(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan excludes target file context when keywords are not present."""
        driver = test_driver_planning
        mock_task = {
            'task_id': 'mock_task',
            'task_name': 'Implement a new API endpoint',
            'description': 'Create a file in src/api/routes.',
            'priority': 'High', 'status': 'Not Started'
        }
        driver.generate_solution_plan(mock_task)
        called_prompt = mock_invoke_coder_llm.call_args[0][0]
        assert "The primary file being modified for this task is `src/core/automation/workflow_driver.py`." not in called_prompt

    @patch.object(WorkflowDriver, '_invoke_coder_llm', return_value="1. Step.")
    def test_generate_solution_plan_prioritizes_target_file_field(self, mock_invoke_coder_llm, test_driver_planning):
        """Test generate_solution_plan prioritizes the 'target_file' field over heuristic."""
        driver = test_driver_planning
        mock_task = {
            'task_id': 'mock_task',
            'task_name': 'Enhance the WorkflowDriver', # Contains heuristic keyword
            'description': 'Modify the file src/core/automation/workflow_driver.py.', # Contains heuristic keyword
            'priority': 'High', 'status': 'Not Started',
            'target_file': 'src/some_other_file.py' # Explicit target file
        }
        driver.generate_solution_plan(mock_task)
        called_prompt = mock_invoke_coder_llm.call_args[0][0]
        # Should use the target_file field
        assert "The primary file being modified for this task is specified as `src/some_other_file.py` in the task metadata." in called_prompt
        # Should NOT use the heuristic based on name/description
        assert "The primary file being modified for this task is `src/core/automation/workflow_driver.py`." not in called_prompt


    # --- Tests for generate_user_actionable_steps ---
    def test_generate_user_actionable_steps_empty(self, test_driver_planning):
        driver = test_driver_planning
        assert driver.generate_user_actionable_steps([]) == ""

    def test_generate_user_actionable_steps_single(self, test_driver_planning):
        driver = test_driver_planning
        result = driver.generate_user_actionable_steps(["Single step"])
        assert result == "1.  - [ ] Single step\n"

    def test_generate_user_actionable_steps_multiple(self, test_driver_planning):
        driver = test_driver_planning
        steps = ["Step 1", "Step 2", "Step 3"]
        expected = (
            "1.  - [ ] Step 1\n"
            "2.  - [ ] Step 2\n"
            "3.  - [ ] Step 3\n"
        )
        assert driver.generate_user_actionable_steps(steps) == expected

    def test_generate_user_actionable_steps_special_chars(self, test_driver_planning):
        driver = test_driver_planning
        steps = ["Use <script>", "Escape > & < tags", "Math: 5 > 3"]
        expected = (
            f"1.  - [ ] {html.escape('Use <script>')}\n"
            f"2.  - [ ] {html.escape('Escape > & < tags')}\n"
            f"3.  - [ ] {html.escape('Math: 5 > 3')}\n"
        )
        result = driver.generate_user_actionable_steps(steps)
        assert result == expected, "Special characters should be escaped using html.escape."

    def test_generate_user_actionable_steps_invalid_input_type(self, test_driver_planning):
        driver = test_driver_planning
        with pytest.raises(TypeError):
            driver.generate_user_actionable_steps("not a list")
        with pytest.raises(TypeError):
            driver.generate_user_actionable_steps([1, 2, 3])
        with pytest.raises(TypeError):
            driver.generate_user_actionable_steps(["valid", 123])

