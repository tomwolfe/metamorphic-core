# tests/test_workflow_task_management.py

import pytest
import os
import json
import html
from src.core.automation.workflow_driver import WorkflowDriver, Context
import logging
from unittest.mock import MagicMock, patch

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_task_management(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation as they are not needed for task management tests
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'):
        driver = WorkflowDriver(context)
        # driver.llm_orchestrator = MagicMock() # Not needed for these tests
        yield driver

def create_mock_roadmap_file(content, tmp_path, is_json=True):
    """Creates a mock roadmap file in the temporary directory."""
    if is_json:
        file_path = tmp_path / "ROADMAP.json"
    else:
        file_path = tmp_path / "ROADMAP.txt"
    with open(file_path, "w") as f:
        f.write(content)
    return str(file_path)

class TestWorkflowTaskManagement:

    # --- Tests for load_roadmap ---
    def test_load_roadmap_valid_json(self, test_driver_task_management, tmp_path):
        driver = test_driver_task_management
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
        # load_roadmap is called with the full path by start_workflow, but we test it directly here
        # It needs to use the provided path directly.
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 1
        assert tasks[0]["task_id"] == "Task1"
        assert tasks[0]["priority"] == "High"
        assert tasks[0]["task_name"] == "Test Task"
        assert tasks[0]["status"] == "Not Started"
        assert tasks[0]["description"] == "A test task description."
        assert "depends_on" in tasks[0] # Check that depends_on key is present
        assert tasks[0]["depends_on"] == [] # Check default value is empty list

    def test_load_roadmap_file_not_found(self, test_driver_task_management, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_task_management
        non_existent_file = str(tmp_path / "NON_EXISTENT_ROADMAP.json")
        tasks = driver.load_roadmap(non_existent_file)
        assert len(tasks) == 0
        assert f"ROADMAP.json file not found at path: {non_existent_file}" in caplog.text

    def test_load_roadmap_invalid_json(self, test_driver_task_management, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_task_management
        roadmap_content = "This is not a valid JSON file."
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 0
        assert "Invalid JSON in roadmap file" in caplog.text

    def test_load_roadmap_file_size_limit(self, test_driver_task_management, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_task_management
        long_string = "A" * 20000
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
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 0
        assert "file exceeds maximum allowed size" in caplog.text

    def test_load_roadmap_missing_tasks_key(self, test_driver_task_management, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_task_management
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
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 0
        assert "ROADMAP.json must contain a 'tasks' key." in caplog.text

    def test_load_roadmap_tasks_not_a_list(self, test_driver_task_management, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_task_management
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
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 0
        assert "'tasks' must be a list" in caplog.text

    def test_load_roadmap_invalid_task_format(self, test_driver_task_management, tmp_path, caplog):
        """Test load_roadmap skips invalid task formats within the list."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        tasks = [
            "not a dict",
            {'task_id': 't3', 'status': 'Not Started'},
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'High', 'depends_on': []},
            {'task_id': 't2', 'status': 'Not Started', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High', 'depends_on': []}
        ]
        roadmap_content = json.dumps({"tasks": tasks})
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = driver.load_roadmap(roadmap_file)
        # Corrected assertion based on analysis
        assert len(tasks) == 2
        assert tasks[0]['task_id'] == 't1'
        assert tasks[1]['task_id'] == 't2'
        assert "Skipping invalid task (not a dictionary): not a dict" in caplog.text
        assert "Task missing required keys: {'task_id': 't3', 'status': 'Not Started'}" in caplog.text
        # Removed incorrect assertion about t2 missing keys


    def test_load_roadmap_list_with_invalid_task_id(self, test_driver_task_management, tmp_path, caplog):
        """Test load_roadmap skips tasks with invalid task_id format."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        # Moved roadmap_content inside the function
        roadmap_content = """
        {
            "phase": "Test Phase",
            "phase_goal": "Goal",
            "success_metrics": [],
            "tasks": [
                {
                    "task_id": "invalid/id",
                    "priority": "High",
                    "task_name": "Test Task",
                    "status": "Not Started",
                    "description": "A test task description."
                },
                {
                    "task_id": "t2",
                    "priority": "High",
                    "task_name": "Test Task 2",
                    "status": "Not Started",
                    "description": "Another test task description."
                }
            ],
            "next_phase_actions": [],
            "current_focus": "Test focus"
        }
        """
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 1
        assert tasks[0]['task_id'] == 't2'
        # Corrected assertion to include single quotes around the invalid ID
        assert "Skipping task with invalid task_id format: 'invalid/id'" in caplog.text


    def test_load_roadmap_task_name_too_long(self, test_driver_task_management, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
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
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 0
        assert "Task Name" in caplog.text and "exceeds 150 characters" in caplog.text

    def test_load_roadmap_handles_html_in_description(self, test_driver_task_management, tmp_path, caplog):
        """Tests that description field is escaped to prevent JS injection"""
        caplog.set_level(logging.ERROR)
        driver = test_driver_task_management
        roadmap_content = f"""
        {{
            "phase": "Test Phase",
            "phase_goal": "Goal",
            "success_metrics": [],
            "tasks": [
                {{
                    "task_id": "HtmlTask",
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
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 1
        expected_description = html.escape("<script> test</script>")
        assert tasks[0]["description"] == expected_description, f"Expected escaped version of '<script> test</script>', got '{tasks[0]['description']}'"

    # --- Tests for select_next_task ---
    def test_select_next_task_valid_list_with_not_started(self, test_driver_task_management):
        """Test select_next_task returns the first 'Not Started' task."""
        driver = test_driver_task_management
        tasks = [
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 't2', 'status': 'Not Started', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High', 'depends_on': []},
            {'task_id': 't3', 'status': 'Not Started', 'task_name': 'Task 3', 'description': 'Desc', 'priority': 'Medium', 'depends_on': []}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 't2'

    def test_select_next_task_valid_list_no_not_started(self, test_driver_task_management):
        """Test select_next_task returns None when no 'Not Started' tasks exist."""
        driver = test_driver_task_management
        tasks = [
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 't2', 'status': 'Completed', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High', 'depends_on': []}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is None

    def test_select_next_task_empty_list(self, test_driver_task_management):
        """Test select_next_task returns None for an empty list."""
        driver = test_driver_task_management
        tasks = []
        next_task = driver.select_next_task(tasks)
        assert next_task is None

    def test_select_next_task_invalid_input_not_list(self, test_driver_task_management, caplog):
        """Test select_next_task handles non-list input gracefully."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        tasks = "not a list"
        next_task = driver.select_next_task(tasks)
        assert next_task is None
        assert "select_next_task received non-list input" in caplog.text


    def test_select_next_task_list_with_invalid_task_format(self, test_driver_task_management, caplog):
        """Test select_next_task skips invalid task formats within the list."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        tasks = [
            "not a dict",
            {'task_id': 't3', 'status': 'Not Started'},
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'High', 'depends_on': []},
            {'task_id': 't2', 'status': 'Not Started', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High', 'depends_on': []}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is not None
        # Corrected assertion based on analysis
        assert next_task['task_id'] == 't2'

        assert "Skipping invalid task format in list: not a dict" in caplog.text
        assert "Skipping invalid task format in list: {'task_id': 't3', 'status': 'Not Started'}" in caplog.text


    def test_select_next_task_list_with_invalid_task_id(self, test_driver_task_management, caplog):
        """Test select_next_task skips tasks with invalid task_id format."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        tasks = [
            {'task_id': 'invalid/id', 'status': 'Not Started', 'task_name': 'Task Invalid', 'description': 'Desc', 'priority': 'High', 'depends_on': []},
            {'task_id': 't2', 'status': 'Not Started', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High', 'depends_on': []}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 't2'
        assert "Skipping task with invalid task_id format: 'invalid/id'" in caplog.text

    # --- Tests for _is_valid_task_id ---
    def test_is_valid_task_id_valid_formats(self, test_driver_task_management):
        """Test _is_valid_task_id with valid task ID formats."""
        driver = test_driver_task_management
        assert driver._is_valid_task_id("task_1_1") is True
        assert driver._is_valid_task_id("Task-ID-2") is True
        assert driver._is_valid_task_id("task123") is True
        assert driver._is_valid_task_id("a_b-c_1-2") is True
        assert driver._is_valid_task_id("justletters") is True
        assert driver._is_valid_task_id("just123") is True
        assert driver._is_valid_task_id("a") is True
        assert driver._is_valid_task_id("1") is True
        assert driver._is_valid_task_id("a-") is True
        assert driver._is_valid_task_id("a_") is True


    def test_is_valid_task_id_invalid_formats(self, test_driver_task_management):
        """Test _is_valid_task_id with invalid task ID formats."""
        driver = test_driver_task_management
        assert driver._is_valid_task_id("invalid/id") is False
        assert driver._is_valid_task_id("..") is False
        assert driver._is_valid_task_id("../task") is False
        assert driver._is_valid_task_id("task id") is False
        assert driver._is_valid_task_id("task!@#") is False
        assert driver._is_valid_task_id("") is False
        assert driver._is_valid_task_id(None) is False
        assert driver._is_valid_task_id(123) is False
        assert driver._is_valid_task_id("task.") is False
        assert driver._is_valid_task_id(".task") is False
        assert driver._is_valid_task_id("-task") is False

    # --- NEW TESTS FOR depends_on LOADING AND VALIDATION ---

    def test_load_roadmap_with_valid_depends_on(self, test_driver_task_management, tmp_path):
        """Test loading a task with a valid 'depends_on' list."""
        driver = test_driver_task_management
        roadmap_content = """
        {
            "tasks": [
                {
                    "task_id": "task_with_deps",
                    "priority": "High",
                    "task_name": "Task with Dependencies",
                    "status": "Not Started",
                    "description": "This task depends on others.",
                    "depends_on": ["task_1_7_1", "task_1_7_2"]
                },
                {
                    "task_id": "task_without_deps",
                    "priority": "High",
                    "task_name": "Task without Dependencies",
                    "status": "Not Started",
                    "description": "This task has no dependencies."
                }
            ]
        }
        """
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = driver.load_roadmap(roadmap_file)
        assert len(tasks) == 2
        task_with_deps = next(t for t in tasks if t['task_id'] == 'task_with_deps')
        task_without_deps = next(t for t in tasks if t['task_id'] == 'task_without_deps')

        assert "depends_on" in task_with_deps
        assert task_with_deps["depends_on"] == ["task_1_7_1", "task_1_7_2"]

        assert "depends_on" in task_without_deps
        assert task_without_deps["depends_on"] == [] # Default value

    def test_load_roadmap_depends_on_not_a_list(self, test_driver_task_management, tmp_path, caplog):
        """Test loading a task where 'depends_on' is not a list."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        roadmap_content = """
        {
            "tasks": [
                {
                    "task_id": "task_invalid_deps_type",
                    "priority": "High",
                    "task_name": "Task with Invalid Deps Type",
                    "status": "Not Started",
                    "description": "Deps field is not a list.",
                    "depends_on": "not a list"
                },
                 {
                    "task_id": "task_valid",
                    "priority": "High",
                    "task_name": "Valid Task",
                    "status": "Not Started",
                    "description": "This task is valid."
                }
            ]
        }
        """
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = driver.load_roadmap(roadmap_file)

        assert len(tasks) == 1 # The invalid task should be skipped
        assert tasks[0]['task_id'] == 'task_valid'
        assert "Skipping task task_invalid_deps_type: 'depends_on' field is not a list." in caplog.text

    def test_load_roadmap_depends_on_list_with_invalid_ids(self, test_driver_task_management, tmp_path, caplog):
        """Test loading a task where 'depends_on' list contains invalid task_ids."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        roadmap_content = """
        {
            "tasks": [
                {
                    "task_id": "task_invalid_deps_ids",
                    "priority": "High",
                    "task_name": "Task with Invalid Deps IDs",
                    "status": "Not Started",
                    "description": "Deps list contains invalid IDs.",
                    "depends_on": ["task_1_7_1", 123, "invalid/id", "task_1_7_2"]
                },
                 {
                    "task_id": "task_valid",
                    "priority": "High",
                    "task_name": "Valid Task",
                    "status": "Not Started",
                    "description": "This task is valid."
                }
            ]
        }
        """
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = driver.load_roadmap(roadmap_file)

        assert len(tasks) == 1 # The invalid task should be skipped
        assert tasks[0]['task_id'] == 'task_valid'
        # Check log messages for invalid elements - only the first invalid one is logged
        assert "Skipping task task_invalid_deps_ids: Invalid task_id '123' found in 'depends_on' list." in caplog.text
        # The assertion below will now pass because the loop breaks at '123'
        assert "Skipping task task_invalid_deps_ids: Invalid task_id 'invalid/id' found in 'depends_on' list." not in caplog.text


    def test_load_roadmap_depends_on_list_with_non_strings(self, test_driver_task_management, tmp_path, caplog):
        """Test loading a task where 'depends_on' list contains non-string elements."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        roadmap_content = """
        {
            "tasks": [
                {
                    "task_id": "task_invalid_deps_elements",
                    "priority": "High",
                    "task_name": "Task with Invalid Deps Elements",
                    "status": "Not Started",
                    "description": "Deps list contains non-strings.",
                    "depends_on": ["task_1_7_1", 123, {"task": "id"}]
                },
                 {
                    "task_id": "task_valid",
                    "priority": "High",
                    "task_name": "Valid Task",
                    "status": "Not Started",
                    "description": "This task is valid."
                }
            ]
        }
        """
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = driver.load_roadmap(roadmap_file)

        assert len(tasks) == 1 # The invalid task should be skipped
        assert tasks[0]['task_id'] == 'task_valid'
        # Check log messages for invalid elements - only the first invalid one is logged
        assert "Skipping task task_invalid_deps_elements: Invalid task_id '123' found in 'depends_on' list." in caplog.text
        # The assertion below will now pass because the loop breaks at '123'


    # --- NEW TESTS FOR DEPENDENCY-AWARE TASK SELECTION ---

    def test_select_next_task_with_completed_dependencies(self, test_driver_task_management):
        """Test selecting a 'Not Started' task whose 'depends_on' tasks are all 'Completed'."""
        driver = test_driver_task_management
        tasks = [
            {'task_id': 'dep1', 'status': 'Completed', 'task_name': 'Dep 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'dep2', 'status': 'Completed', 'task_name': 'Dep 2', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_with_deps', 'status': 'Not Started', 'task_name': 'Task with Deps', 'description': 'Desc', 'priority': 'High', 'depends_on': ['dep1', 'dep2']}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 'task_with_deps'

    def test_select_next_task_skip_not_started_dependency(self, test_driver_task_management, caplog):
        """Test skipping a 'Not Started' task if one of its dependencies is 'Not Started'."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_task_management
        # Corrected test data: task_with_deps is the first 'Not Started' task
        tasks = [
            {'task_id': 'task_with_deps', 'status': 'Not Started', 'task_name': 'Task with Deps', 'description': 'Desc', 'priority': 'High', 'depends_on': ['dep1']},
            {'task_id': 'dep1', 'status': 'Not Started', 'task_name': 'Dep 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []}
        ]
        next_task = driver.select_next_task(tasks)
        # Corrected assertion based on analysis: task_with_deps should be skipped, dep1 should be selected
        assert next_task is not None
        assert next_task['task_id'] == 'dep1'
        assert "Skipping task task_with_deps: Dependency 'dep1' status is 'Not Started' (requires 'Completed')." in caplog.text


    def test_select_next_task_skip_in_progress_dependency(self, test_driver_task_management, caplog):
        """Test skipping a 'Not Started' task if one of its dependencies is 'In Progress'."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_task_management
        tasks = [
            {'task_id': 'dep1', 'status': 'In Progress', 'task_name': 'Dep 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_with_deps', 'status': 'Not Started', 'task_name': 'Task with Deps', 'description': 'Desc', 'priority': 'High', 'depends_on': ['dep1']}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is None
        assert "Skipping task task_with_deps: Dependency 'dep1' status is 'In Progress' (requires 'Completed')." in caplog.text


    def test_select_next_task_skip_blocked_dependency(self, test_driver_task_management, caplog):
        """Test skipping a 'Not Started' task if one of its dependencies is 'Blocked'."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_task_management
        tasks = [
            {'task_id': 'dep1', 'status': 'Blocked', 'task_name': 'Dep 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_with_deps', 'status': 'Not Started', 'task_name': 'Task with Deps', 'description': 'Desc', 'priority': 'High', 'depends_on': ['dep1']}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is None
        assert "Skipping task task_with_deps: Dependency 'dep1' status is 'Blocked' (requires 'Completed')." in caplog.text


    def test_select_next_task_skip_non_existent_dependency(self, test_driver_task_management, caplog):
        """Test skipping a 'Not Started' task if one of its dependencies does not exist in the tasks list."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_task_management
        tasks = [
            {'task_id': 'task_with_deps', 'status': 'Not Started', 'task_name': 'Task with Deps', 'description': 'Desc', 'priority': 'High', 'depends_on': ['non_existent_dep']}
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is None
        assert "Skipping task task_with_deps: Dependency 'non_existent_dep' not found in roadmap." in caplog.text


    def test_select_next_task_multiple_not_started_with_deps(self, test_driver_task_management):
        """Test selecting the correct task when multiple 'Not Started' tasks exist, but only the first one has its dependencies met."""
        driver = test_driver_task_management
        tasks = [
            {'task_id': 'dep1', 'status': 'Completed', 'task_name': 'Dep 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_ready', 'status': 'Not Started', 'task_name': 'Task Ready', 'description': 'Desc', 'priority': 'High', 'depends_on': ['dep1']}, # This one is ready
            {'task_id': 'dep2', 'status': 'Not Started', 'task_name': 'Dep 2', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_not_ready', 'status': 'Not Started', 'task_name': 'Task Not Ready', 'description': 'Desc', 'priority': 'Medium', 'depends_on': ['dep2']} # This one is not ready
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 'task_ready' # Should select the first one that is ready

    def test_select_next_task_empty_depends_on_list(self, test_driver_task_management):
        """Test selecting a 'Not Started' task with an empty 'depends_on' list (should behave like no dependencies)."""
        driver = test_driver_task_management
        tasks = [
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_empty_deps', 'status': 'Not Started', 'task_name': 'Task Empty Deps', 'description': 'Desc', 'priority': 'High', 'depends_on': []} # Empty depends_on
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 'task_empty_deps'

    def test_select_next_task_depends_on_field_missing(self, test_driver_task_management):
        """Test selecting a 'Not Started' task where the 'depends_on' field is missing (should behave like no dependencies)."""
        driver = test_driver_task_management
        tasks = [
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_missing_deps', 'status': 'Not Started', 'task_name': 'Task Missing Deps', 'description': 'Desc', 'priority': 'High'} # depends_on field missing
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 'task_missing_deps'

    def test_select_next_task_invalid_dependency_id_format_in_list(self, test_driver_task_management, caplog):
        """Test skipping a task if its depends_on list contains an invalid task ID format."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_task_management
        tasks = [
            {'task_id': 'dep1', 'status': 'Completed', 'task_name': 'Dep 1', 'description': 'Desc', 'priority': 'Low', 'depends_on': []},
            {'task_id': 'task_invalid_dep_format', 'status': 'Not Started', 'task_name': 'Task Invalid Dep Format', 'description': 'Desc', 'priority': 'High', 'depends_on': ['dep1', 'invalid/dep']} # Invalid format in deps list
        ]
        next_task = driver.select_next_task(tasks)
        assert next_task is None
        assert "Skipping task task_invalid_dep_format: Invalid task_id 'invalid/dep' found in 'depends_on' list." in caplog.text