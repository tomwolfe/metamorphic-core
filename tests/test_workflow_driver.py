# tests/test_workflow_driver.py
import pytest
from src.core.automation.workflow_driver import WorkflowDriver, Context
import os
from unittest.mock import patch, mock_open
import logging
import json
from scripts.generate_roadmap_md import generate_roadmap_md
import html
import shutil

# Set up logging for tests
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@pytest.fixture
def test_driver(tmp_path):
    context = Context(str(tmp_path))
    return WorkflowDriver(context)

def create_mock_roadmap_file(content, tmp_path, is_json=True):
    """Creates a mock roadmap file in the temporary directory."""
    if is_json:
        file_path = tmp_path / "ROADMAP.json"
    else:
        file_path = tmp_path / "ROADMAP.txt"
    with open(file_path, "w") as f:
        f.write(content)
    return str(file_path)

def test_load_roadmap_valid_json(test_driver, tmp_path):
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            {
                "task_id": "Task1",
                "priority": "High",
                "task_name": "Test Task",
                "status": "Not Started",
                "description": "A test task description."
            }
        ],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 1
    assert tasks[0]["task_id"] == "Task1"
    assert tasks[0]["priority"] == "High"
    assert tasks[0]["task_name"] == "Test Task"
    assert tasks[0]["status"] == "Not Started"
    assert tasks[0]["description"] == "A test task description."

def test_load_roadmap_file_not_found(test_driver, tmp_path, caplog):
    caplog.set_level(logging.ERROR)
    non_existent_file = tmp_path / "NON_EXISTENT_ROADMAP.json"
    tasks = test_driver.load_roadmap(str(non_existent_file))
    assert len(tasks) == 0
    assert "ROADMAP.json file not found" in caplog.text

def test_load_roadmap_invalid_json(test_driver, tmp_path, caplog):
    caplog.set_level(logging.ERROR)
    roadmap_content = "This is not a valid JSON file."
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Invalid JSON in roadmap file" in caplog.text

def test_load_roadmap_file_size_limit(test_driver, tmp_path, caplog):
    caplog.set_level(logging.ERROR)
    long_string = "A" * 11000
    roadmap_content = f"""
    {{
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            {{
                "task_id": "Task1",
                "priority": "High",
                "task_name": "Test Task",
                "status": "Not Started",
                "description": "{long_string}"
            }}
        ],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }}
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "file exceeds maximum allowed size" in caplog.text

def test_load_roadmap_missing_tasks_key(test_driver, tmp_path, caplog):
    caplog.set_level(logging.ERROR)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "ROADMAP.json must contain a 'tasks' key" in caplog.text

def test_load_roadmap_tasks_not_a_list(test_driver, tmp_path, caplog):
    caplog.set_level(logging.ERROR)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": "not a list",
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "'tasks' must be a list" in caplog.text

def test_load_roadmap_invalid_task_format(test_driver, tmp_path, caplog):
    caplog.set_level(logging.WARNING)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            "not a dictionary"
        ],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Skipping invalid task (not a dictionary)" in caplog.text

def test_load_roadmap_missing_required_keys(test_driver, tmp_path, caplog):
    caplog.set_level(logging.WARNING)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            {
                "task_name": "Test Task",
                "status": "Not Started",
                "description": "A test task description."
            }
        ],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Task missing required keys" in caplog.text

def test_load_roadmap_invalid_task_id(test_driver, tmp_path, caplog):
    caplog.set_level(logging.WARNING)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            {
                "task_id": "Invalid/Task",
                "priority": "High",
                "task_name": "Test Task",
                "status": "Not Started",
                "description": "A test task description."
            }
        ],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Invalid task_id" in caplog.text

def test_load_roadmap_task_name_too_long(test_driver, tmp_path, caplog):
    caplog.set_level(logging.WARNING)
    long_task_name = "A" * 151
    roadmap_content = f"""
    {{
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            {{
                "task_id": "LongTask",
                "priority": "High",
                "task_name": "{long_task_name}",
                "status": "Not Started",
                "description": "A test task description."
            }}
        ],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }}
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Task Name" in caplog.text and "exceeds 150 characters" in caplog.text

def test_load_roadmap_handles_js_vulnerability_for_description(test_driver, tmp_path, caplog):
    """Tests that description field is escaped to prevent JS injection"""
    caplog.set_level(logging.ERROR)
    roadmap_content = f"""
    {{
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            {{
                "task_id": "LongTask",
                "priority": "High",
                "task_name": "Test Name",
                "status": "Not Started",
                "description": "<script> test</script>"
            }}
        ],
        "next_phase_actions": [],
        "current_focus": "Test focus"
    }}
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 1
    # Expect the escaped HTML version
    expected_description = html.escape("<script> test</script>")
    assert tasks[0]["description"] == expected_description, f"Expected escaped version of '<script> test</script>', got '{tasks[0]['description']}'"

def test_file_exists_existing(test_driver, tmp_path):
    test_file = tmp_path / "test.txt"
    test_file.write_text("content")
    assert test_driver.file_exists(str(test_file)) is True

def test_file_exists_non_existing(test_driver, tmp_path):
    non_existing_file = tmp_path / "nonexist.txt"
    assert test_driver.file_exists(str(non_existing_file)) is False

def test_list_files(test_driver, tmp_path):
    temp_test_dir = tmp_path / "test_list_files_temp_dir"  # Create a unique temp dir for this test
    temp_test_dir.mkdir()
    try:
        (temp_test_dir / "file1.txt").write_text("content")
        (temp_test_dir / "file2.txt").write_text("content")
        subdir = temp_test_dir / "subdir"
        subdir.mkdir()
        (subdir / "file_in_subdir.txt").write_text("content")

        context = Context(str(temp_test_dir)) # Use the unique temp dir in context
        driver = WorkflowDriver(context)
        entries = driver.list_files()
        expected = [
            {'name': 'file1.txt', 'status': 'file'},
            {'name': 'file2.txt', 'status': 'file'},
            {'name': 'subdir', 'status': 'directory'}
        ]
        entries_set = {tuple(sorted(d.items())) for d in entries}
        expected_set = {tuple(sorted(d.items())) for d in expected}
        assert entries_set == expected_set
    finally:
        try:
            shutil.rmtree(str(temp_test_dir)) # Cleanup the unique temp dir
        except OSError as e:
            logger.warning(f"Failed to remove directory {temp_test_dir}: {e}")


    def test_generate_user_actionable_steps_empty(self, test_driver):
        assert test_driver.generate_user_actionable_steps([]) == ""

    def test_generate_user_actionable_steps_single(self, test_driver):
        result = test_driver.generate_user_actionable_steps(["Single step"])
        assert result == "1.  - [ ] Single step\n"

    def test_generate_user_actionable_steps_multiple(self, test_driver):
        steps = ["Step 1", "Step 2", "Step 3"]
        expected = (
            "1.  - [ ] Step 1\n"
            "2.  - [ ] Step 2\n"
            "3.  - [ ] Step 3\n"
        )
        assert test_driver.generate_user_actionable_steps(steps) == expected

    def test_generate_user_actionable_steps_special_chars(self, test_driver):
        steps = ["Use <script>", "Escape > & < tags", "Math: 5 > 3"]
        expected = (
            f"1.  - [ ] {html.escape('Use <script>')}\n"
            f"2.  - [ ] {html.escape('Escape > & < tags')}\n"
            f"3.  - [ ] {html.escape('Math: 5 > 3')}\n"
        )
        result = test_driver.generate_user_actionable_steps(steps)
        assert result == expected, "Special characters should be escaped using html.escape."

    def test_generate_user_actionable_steps_type_error(self, test_driver):
        with pytest.raises(TypeError):
            test_driver.generate_user_actionable_steps("not a list")

        with pytest.raises(TypeError):
            test_driver.generate_user_actionable_steps([1, 2, 3])

        with pytest.raises(TypeError):
            test_driver.generate_user_actionable_steps([{"step": "dict instead of string"}])

    def test_generate_coder_llm_prompts_valid(self, test_driver):
        task = {"task_id": "t1", "priority": "High", "task_name": "Sample Task", "description": "Do something cool."}
        plan = ["Step 1: Define function.", "Step 2: Add logic.", "Step 3: Write tests."]
        prompts = test_driver.generate_coder_llm_prompts(task, plan)
        assert isinstance(prompts, list)
        assert len(prompts) > 0 # Expecting at least one prompt based on current logic
        assert "Sample Task" in prompts[0]
        assert "Do something cool." in prompts[0]
        assert "Step 1: Define function." in prompts[0]
        assert "Requirements:" in prompts[0]
        assert "Prioritize security" in prompts[0]

    def test_generate_coder_llm_prompts_empty_plan(self, test_driver):
        task = {"task_id": "t2", "priority": "Low", "task_name": "Empty Plan Task", "description": "Nothing to do."}
        plan = []
        prompts = test_driver.generate_coder_llm_prompts(task, plan)
        # Depending on implementation, might return one generic prompt or empty list.
        # Current implementation generates one prompt even for empty plan.
        assert isinstance(prompts, list)
        assert len(prompts) == 1 # Adjust if implementation changes
        # assert "Implement the following steps:" in prompts[0] # Check if the prompt is generated

    def test_generate_coder_llm_prompts_invalid_task_type(self, test_driver):
        with pytest.raises(TypeError, match="Input 'task' must be a dictionary"):
            test_driver.generate_coder_llm_prompts("not a dict", ["Step 1"])

    def test_generate_coder_llm_prompts_invalid_plan_type(self, test_driver):
        task = {"task_id": "t3", "priority": "High", "task_name": "Invalid Plan", "description": "Desc"}
        with pytest.raises(TypeError, match="Input 'solution_plan' must be a list of strings"):
            test_driver.generate_coder_llm_prompts(task, "not a list")
        with pytest.raises(TypeError, match="Input 'solution_plan' must be a list of strings"):
            test_driver.generate_coder_llm_prompts(task, [1, 2, 3]) # List of non-strings

    def test_generate_coder_llm_prompts_missing_task_keys(self, test_driver):
        task = {"task_id": "t4", "priority": "High"} # Missing name and description
        plan = ["Step 1"]
        with pytest.raises(ValueError, match="Task dictionary must contain 'task_name' and 'description' keys"):
            test_driver.generate_coder_llm_prompts(task, plan)

    def test_generate_coder_llm_prompts_html_escaping(test_driver):
        """Test generate_coder_llm_prompts escapes HTML characters in prompt."""
        task = {
            "task_id": "test_task_6",
            "task_name": "Task with <script>alert()</script> tag",
            "description": "Description with <b>bold</b> and &special characters.",
            "priority": "High"
        }
        solution_plan = ["Step 1: Handle <input> safely."]
        prompts = test_driver.generate_coder_llm_prompts(task, solution_plan)
        prompt = prompts[0]

        # Check for proper escaping of HTML tags and special characters
        assert "<script>" in prompt
        assert "</script>" in prompt
        assert "<b>" in prompt
        assert "</b>" in prompt
        assert "<input>" in prompt
        assert "&special" in prompt  # Escaped '&' in description

        # Ensure unescaped versions are not present
        assert "<script>" not in prompt
        assert "</script>" not in prompt
        assert "<b>" not in prompt
        assert "</b>" not in prompt
        assert "<input>" not in prompt
        assert "&" not in prompt  # Assuming no unescaped '&' except in escaped entities

        # Check that other parts of the prompt remain intact
        assert "Task with" in prompt
        assert "Description with" in prompt
        assert "Prioritize security" in prompt

def test_generate_coder_llm_prompts_null_plan(test_driver):
    """Test generate_coder_llm_prompts with None as solution_plan."""
    task = {
        "task_id": "test_task_7",
        "task_name": "Null Plan Task",
        "description": "Task with solution plan set to None.",
        "priority": "Low"
    }
    with pytest.raises(TypeError) as excinfo:
        test_driver.generate_coder_llm_prompts(task, None)
    assert "Input 'solution_plan' must be a list of strings" in str(excinfo.value)