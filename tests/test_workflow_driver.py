# tests/test_workflow_driver.py
import pytest
from src.core.automation.workflow_driver import WorkflowDriver, Context # Import Context
import os
from unittest.mock import patch, mock_open
import logging
import json
# Set up logging for tests
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)
@pytest.fixture
def test_driver(tmp_path):
    context = Context(str(tmp_path)) # Create context with tmp_path
    return WorkflowDriver(context) # Pass context to WorkflowDriver
def create_mock_roadmap_file(content, tmp_path, is_json=True):
    """Creates a mock roadmap file in the temporary directory."""
    if is_json:
        file_path = tmp_path / "ROADMAP.json"
    else:
        file_path = tmp_path / "ROADMAP.txt"  # or any other extension
    with open(file_path, "w") as f:
        f.write(content)
    return str(file_path)
def test_load_roadmap_valid_json(test_driver, tmp_path):
    """Tests loading a valid JSON roadmap file."""
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
        "next_phase_actions": []
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 1
    assert tasks[0]["task_id"] == "Task1"
    assert tasks[0]["priority"] == "High"
    assert tasks[0]["task_name"] == "Test Task"
    assert tasks[0]["status"] == "Not Started"
    assert tasks[0]["description"] == "A test task description."
def test_load_roadmap_file_not_found(test_driver, tmp_path, caplog):
    """Tests the scenario where the roadmap file is not found."""
    caplog.set_level(logging.ERROR)
    non_existent_file = tmp_path / "NON_EXISTENT_ROADMAP.json"
    tasks = test_driver.load_roadmap(str(non_existent_file))
    assert len(tasks) == 0
    assert "ROADMAP.json file not found" in caplog.text
def test_load_roadmap_invalid_json(test_driver, tmp_path, caplog):
    """Tests loading an invalid JSON roadmap file."""
    caplog.set_level(logging.ERROR)
    roadmap_content = "This is not a valid JSON file."
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Invalid JSON in roadmap file" in caplog.text
def test_load_roadmap_file_size_limit(test_driver, tmp_path, caplog):
    """Tests the roadmap file size limit."""
    caplog.set_level(logging.ERROR)
    long_string = "A" * 11000  # Create a string longer than 10KB
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
        "next_phase_actions": []
    }}
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "file exceeds maximum allowed size" in caplog.text
def test_load_roadmap_missing_tasks_key(test_driver, tmp_path, caplog):
    """Tests loading a roadmap with a missing 'tasks' key."""
    caplog.set_level(logging.ERROR)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "next_phase_actions": []
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "ROADMAP.json must contain a 'tasks' list" in caplog.text
def test_load_roadmap_tasks_not_a_list(test_driver, tmp_path, caplog):
    """Tests loading a roadmap where 'tasks' is not a list."""
    caplog.set_level(logging.ERROR)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": "not a list",
        "next_phase_actions": []
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "'tasks' must be a list" in caplog.text
def test_load_roadmap_invalid_task_format(test_driver, tmp_path, caplog):
    """Tests loading a roadmap with an invalid task (not a dictionary)."""
    caplog.set_level(logging.WARNING)
    roadmap_content = """
    {
        "phase": "Test Phase",
        "phase_goal": "Goal",
        "success_metrics": [],
        "tasks": [
            "not a dictionary"
        ],
        "next_phase_actions": []
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Skipping invalid task (not a dictionary)" in caplog.text
def test_load_roadmap_missing_required_keys(test_driver, tmp_path, caplog):
    """Tests loading a roadmap with tasks missing required keys."""
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
        "next_phase_actions": []
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Task missing required keys" in caplog.text
def test_load_roadmap_invalid_task_id(test_driver, tmp_path, caplog):
    """Tests loading a roadmap with an invalid task_id."""
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
        "next_phase_actions": []
    }
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Invalid task_id" in caplog.text
def test_load_roadmap_task_name_too_long(test_driver, tmp_path, caplog):
    """Tests loading a roadmap with a task name that's too long."""
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
        "next_phase_actions": []
    }}
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0
    assert "Task Name" in caplog.text and "exceeds 150 characters" in caplog.text
def test_load_roadmap_handles_js_vulnerability_for_description(test_driver, tmp_path, caplog):
    """Tests if the load_roadmap function handles potential javascript injection attacks in description field to ensure no code can run"""
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
        "next_phase_actions": []
    }}
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path, is_json=True)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 1
    # Check that the script tags were properly escaped
    assert tasks[0]["description"] == "<script> test</script>", "Javascript was not properly escaped"
def test_file_exists_existing(test_driver, tmp_path):
    test_file = tmp_path / "test.txt"
    test_file.write_text("content")
    assert test_driver.file_exists(str(test_file)) is True
def test_file_exists_non_existing(test_driver, tmp_path):
    non_existing_file = tmp_path / "nonexist.txt"
    assert test_driver.file_exists(str(non_existing_file)) is False
def test_list_files(test_driver, tmp_path):
    (tmp_path / "file1.txt").write_text("content")
    (tmp_path / "file2.txt").write_text("content")
    subdir = tmp_path / "subdir"
    subdir.mkdir()
    (subdir / "file_in_subdir.txt").write_text("content")
    entries = test_driver.list_files()
    expected = [{'name': 'file1.txt', 'status': 'file'}, {'name': 'file2.txt', 'status': 'file'}, {'name': 'subdir', 'status': 'directory'}]
    entries_set = {tuple(sorted(d.items())) for d in entries}
    expected_set = {tuple(sorted(d.items())) for d in expected}
    assert entries_set == expected_set