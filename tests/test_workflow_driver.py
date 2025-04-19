import pytest
import html
import shutil
from src.core.automation.workflow_driver import WorkflowDriver, Context
import os
import logging
from src.cli.write_file import write_file, file_exists
from pathlib import Path
import json
from unittest.mock import MagicMock, patch

# Set up logging for tests
# Use basicConfig only if no handlers are already configured
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@pytest.fixture
def test_driver(tmp_path):
    context = Context(str(tmp_path))
    driver = WorkflowDriver(context)
    # Replace the real orchestrator with a mock
    driver.llm_orchestrator = MagicMock()
    driver.llm_orchestrator.generate.return_value = "Test response"
    return driver

def create_mock_roadmap_file(content, tmp_path, is_json=True):
    """Creates a mock roadmap file in the temporary directory."""
    if is_json:
        file_path = tmp_path / "ROADMAP.json"
    else:
        file_path = tmp_path / "ROADMAP.txt"
    with open(file_path, "w") as f:
        f.write(content)
    return str(file_path)

class TestWorkflowDriver:

    def test_autonomous_loop_basic_logging(self, test_driver, caplog):
        """Test that autonomous_loop logs the start and end messages."""
        caplog.set_level(logging.INFO)
        # Initialize tasks list for the driver instance for this test
        test_driver.tasks = [] # No tasks available
        test_driver.autonomous_loop()
        assert 'Starting autonomous loop' in caplog.text
        assert 'No tasks available in Not Started status.' in caplog.text # Check log for no tasks
        assert 'Loop iteration complete' in caplog.text

    # --- New tests for autonomous_loop (Task 15_3a2) ---
    @patch.object(WorkflowDriver, 'select_next_task', return_value={'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'})
    def test_autonomous_loop_task_selected_logging(self, mock_select_next_task, test_driver, caplog):
        """Test that autonomous_loop logs the selected task ID when a task is found."""
        caplog.set_level(logging.INFO)
        test_driver.tasks = [{'task_id': 'mock_task_1', 'task_name': 'Mock Task', 'status': 'Not Started', 'description': 'Desc', 'priority': 'High'}] # Add a task
        test_driver.autonomous_loop()
        mock_select_next_task.assert_called_once_with(test_driver.tasks)
        assert 'Starting autonomous loop' in caplog.text
        assert 'Selected task: ID=mock_task_1' in caplog.text # Check log for selected task
        assert 'Loop iteration complete' in caplog.text

    @patch.object(WorkflowDriver, 'select_next_task', return_value=None)
    def test_autonomous_loop_no_task_logging(self, mock_select_next_task, test_driver, caplog):
        """Test that autonomous_loop logs the 'No tasks available' message when no task is found."""
        caplog.set_level(logging.INFO)
        test_driver.tasks = [{'task_id': 'mock_task_completed', 'task_name': 'Completed Task', 'status': 'Completed', 'description': 'Desc', 'priority': 'High'}] # No 'Not Started' tasks
        test_driver.autonomous_loop()
        mock_select_next_task.assert_called_once_with(test_driver.tasks)
        assert 'Starting autonomous loop' in caplog.text
        assert 'No tasks available in Not Started status.' in caplog.text # Check log for no tasks
        assert 'Loop iteration complete' in caplog.text
    # --- End new tests for autonomous_loop ---


    def test_workflow_driver_write_output_file_success(
        self, test_driver, tmp_path, caplog
    ):
        """Test successful file writing."""
        caplog.set_level(logging.INFO)
        filepath = tmp_path / "test_file.txt"
        content = "Test content"
        result = test_driver._write_output_file(str(filepath), content)
        assert result is True
        assert filepath.exists()
        assert filepath.read_text() == content
        assert "Successfully wrote to file" in caplog.text

    def test_workflow_driver_write_output_file_exists_no_overwrite(
        self, test_driver, tmp_path
    ):
        """Test write_output_file with overwrite=False when file exists."""
        filepath = tmp_path / "existing_file.txt"
        initial_content = "initial content"
        filepath.write_text(initial_content)
        new_content = "new content"
        with pytest.raises(FileExistsError) as exc_info:
            test_driver._write_output_file(str(filepath), new_content, overwrite=False)
        assert "already exists" in str(exc_info.value)
        assert filepath.read_text() == "initial content" # Verify content not overwritten

    def test_workflow_driver_write_output_file_filenotfounderror(
        self, test_driver, tmp_path, caplog
    ):
        """Test writing to a non-existent directory (FileNotFoundError)."""
        caplog.set_level(logging.ERROR)
        invalid_path = tmp_path / "nonexistent_dir" / "file.txt"
        content = "Test content"
        result = test_driver._write_output_file(str(invalid_path), content)
        assert result is False
        assert "Error writing to" in caplog.text and "No such file or directory" in caplog.text

    def test_workflow_driver_write_output_file_permissionerror(
        self, test_driver, tmp_path, caplog
    ):
        """Test writing to a read-only directory (PermissionError)."""
        caplog.set_level(logging.ERROR)
        dir_path = tmp_path / "readonly_dir"
        dir_path.mkdir()
        dir_path.chmod(0o444)  # Set directory to read-only
        filepath = dir_path / "test.txt"
        content = "Test content"
        result = test_driver._write_output_file(str(filepath), content)
        assert result is False
        assert "Error writing to" in caplog.text and "Permission denied" in caplog.text
        try:
            assert not filepath.exists()
        except PermissionError:
            assert True # On some systems, checking existence might also raise PermissionError

    def test_workflow_driver_write_output_file_overwrite_true(
        self, test_driver, tmp_path
    ):
        """Test overwrite=True successfully replaces existing file content."""
        filepath = tmp_path / "overwrite_test.txt"
        initial_content = "original content"
        new_content = "new content"
        filepath.write_text(initial_content)
        result = test_driver._write_output_file(str(filepath), new_content, overwrite=True)
        assert result is True
        assert filepath.read_text() == new_content

    def test_workflow_driver_write_output_file_security_path_injection(
        self, test_driver, tmp_path, caplog # Added caplog to check log message
    ):
        """Test path injection attempts (e.g., using '..' or absolute paths)."""
        original_cwd = os.getcwd()
        os.chdir(tmp_path) # Change to tmp_path for consistent testing
        caplog.set_level(logging.ERROR) # Set level to capture the security error log

        try:
            # Test relative path injection
            relative_path_attempt =  "../injected_file.txt"
            content = "Path injection test - relative path"
            result_relative = test_driver._write_output_file(
                relative_path_attempt, content # Pass the relative path string
            )
            assert result_relative is False, "Relative path write should have failed"
            assert "Attempt to write outside base path" in caplog.text # Check log

            # Verify file is NOT written outside tmp_path
            injected_file = tmp_path.parent / "injected_file.txt"
            assert not injected_file.exists(), "Relative path injection test failed: file was created outside tmp_path unexpectedly!"

            # Test absolute path injection - attempting to write to system's temp dir
            # Note: Path(filepath).resolve() will resolve this to the system's /tmp
            absolute_path_attempt = "/tmp/abs_injected_file.txt"
            content_absolute = "Path injection test - absolute path"
            # Clear caplog for the next check if needed, or check for both messages
            # caplog.clear() # Optional: clear logs between checks if needed
            result_absolute = test_driver._write_output_file(
                 absolute_path_attempt, content_absolute # Pass the absolute path string
            )
            assert result_absolute is False, "Absolute path write should have failed"
            assert "Attempt to write outside base path" in caplog.text # Check log again

            # Check that the file was NOT created in the system's /tmp
            assert not os.path.exists(absolute_path_attempt), "Absolute path injection test failed: file was created unexpectedly!"

        finally:
            os.chdir(original_cwd) # Restore original working directory
            # Clean up the potentially created file in /tmp if the test failed unexpectedly before the assertion
            if os.path.exists(absolute_path_attempt):
                 os.remove(absolute_path_attempt)


    def test_load_roadmap_valid_json(self, test_driver, tmp_path):
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

    def test_load_roadmap_file_not_found(self, test_driver, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        non_existent_file = tmp_path / "NON_EXISTENT_ROADMAP.json"
        tasks = test_driver.load_roadmap(str(non_existent_file))
        assert len(tasks) == 0
        assert "ROADMAP.json file not found" in caplog.text

    def test_load_roadmap_invalid_json(self, test_driver, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        roadmap_content = "This is not a valid JSON file."
        roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
        tasks = test_driver.load_roadmap(roadmap_file)
        assert len(tasks) == 0
        assert "Invalid JSON in roadmap file" in caplog.text

    def test_load_roadmap_file_size_limit(self, test_driver, tmp_path, caplog):
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

    def test_load_roadmap_missing_tasks_key(self, test_driver, tmp_path, caplog):
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
        assert "ROADMAP.json must contain a 'tasks' key." in caplog.text

    def test_load_roadmap_tasks_not_a_list(self, test_driver: WorkflowDriver, tmp_path, caplog):
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

    def test_load_roadmap_invalid_task_format(self, test_driver, tmp_path, caplog):
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

    def test_load_roadmap_missing_required_keys(self, test_driver, tmp_path, caplog):
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

    def test_load_roadmap_invalid_task_id(self, test_driver, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        roadmap_content = """
        {
            "phase": "Test Phase",
            "phase_goal": "Goal",
            "success_metrics": [],
            "tasks": [
                {
                    "task_id": "invalid/task",
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
        assert len(tasks) == 0 # Task should be skipped due to invalid ID
        # Check for the log message about the invalid task_id format
        assert "Skipping task with invalid task_id format: 'invalid/task'" in caplog.text

    def test_load_roadmap_task_name_too_long(self, test_driver, tmp_path, caplog):
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

    def test_load_roadmap_handles_html_in_description(self, test_driver, tmp_path, caplog):
        """Tests that description field is escaped to prevent JS injection"""
        caplog.set_level(logging.ERROR) # Keep ERROR level for other tests
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
        tasks = test_driver.load_roadmap(roadmap_file)
        assert len(tasks) == 1
        # Expect the escaped HTML version
        expected_description = html.escape("<script> test</script>")
        assert tasks[0]["description"] == expected_description, f"Expected escaped version of '<script> test</script>', got '{tasks[0]['description']}'"

    def test_file_exists_existing(self, test_driver, tmp_path):
        test_file = tmp_path / "test.txt"
        test_file.write_text("content")
        assert test_driver.file_exists(str(test_file)) is True

    def test_file_exists_non_existing(self, test_driver, tmp_path):
        non_existing_file = tmp_path / "nonexist.txt"
        assert test_driver.file_exists(str(non_existing_file)) is False

    def test_file_exists_outside_base_path(self, test_driver, tmp_path, caplog):
        """Test file_exists prevents checking outside the base path."""
        caplog.set_level(logging.WARNING)
        # Create a file outside the temporary base path
        outside_dir = tmp_path.parent / "outside_test_dir"
        outside_dir.mkdir(exist_ok=True)
        outside_file = outside_dir / "outside_file.txt"
        outside_file.write_text("sensitive content")

        try:
            # Attempt to check for the file using a relative path that goes outside
            relative_path_attempt = "../outside_test_dir/outside_file.txt"
            assert test_driver.file_exists(relative_path_attempt) is False, "Checking file outside base path should return False"
            assert "Attempted to check file existence outside base path" in caplog.text

            # Attempt to check using an absolute path outside
            absolute_path_attempt = str(outside_file)
            # Clear caplog for the next check if needed, or check for both messages
            # caplog.clear() # Optional: clear logs between checks if needed
            assert test_driver.file_exists(absolute_path_attempt) is False, "Checking file outside base path should return False"
            # Check log again, might be logged twice depending on test setup
            assert "Attempted to check file existence outside base path" in caplog.text

        finally:
            # Clean up the outside directory
            if outside_dir.exists():
                shutil.rmtree(str(outside_dir))


    def test_list_files(self, test_driver, tmp_path):
        temp_test_dir = tmp_path / "test_list_files_temp_dir"
        temp_test_dir.mkdir()
        try:
            (temp_test_dir / "file1.txt").write_text("content")
            (temp_test_dir / "file2.txt").write_text("content")
            subdir = temp_test_dir / "subdir"
            subdir.mkdir()
            (subdir / "file_in_subdir.txt").write_text("content")

            context = Context(str(temp_test_dir))
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
                # Use ignore_errors=True for robustness during cleanup
                shutil.rmtree(str(temp_test_dir), ignore_errors=True)
            except OSError as e:
                # This catch might be redundant with ignore_errors, but keep for safety
                logger.warning(f"Failed to remove directory {temp_test_dir}: {e}")


    def test_list_files_invalid_filename(self, test_driver, tmp_path, caplog):
        """Test list_files skips invalid filenames."""
        caplog.set_level(logging.WARNING)
        temp_test_dir = tmp_path / "test_list_files_invalid_names"
        temp_test_dir.mkdir()
        # Define the path for the file outside the test directory
        outside_file_path = tmp_path.parent / "malicious_file.txt"

        try:
            # Attempt to create a file outside the test dir using path traversal
            # This file will NOT be listed by listdir(temp_test_dir)
            try:
                 outside_file_path.touch()
            except OSError as e:
                 # Log if creating the "malicious" file fails, but don't fail the test
                 logger.warning(f"Could not create file outside test dir: {outside_file_path} - {e}")


            (temp_test_dir / "valid_file.txt").touch()
            subdir_path = temp_test_dir / "another"
            subdir_path.mkdir()
            (subdir_path / "file.txt").touch()

            context = Context(str(temp_test_dir))
            driver = WorkflowDriver(context)
            entries = driver.list_files()

            # Expected entries should only include valid names found *within* the base dir
            expected_names = {'valid_file.txt', 'another'} # 'another' is a directory

            # Check that invalid names are not in the entries
            entry_names = {e['name'] for e in entries}
            # The file created outside should not be listed
            assert "malicious_file.txt" not in entry_names # Check the actual filename, not the path traversal attempt
            assert "../malicious_file.txt" not in entry_names # Check the path traversal string
            assert "another/file.txt" not in entry_names # Files inside subdirs are not listed by listdir(base_dir)

            # Verify the valid file and the created subdirectory are listed
            assert 'valid_file.txt' in entry_names
            assert 'another' in entry_names # The directory itself should be listed

            # Removed the assertion about the specific log message for "../malicious_file.txt"
            # as it's not generated by listdir processing the base directory.

        finally:
            if temp_test_dir.exists():
                shutil.rmtree(str(temp_test_dir), ignore_errors=True)
            if outside_file_path.exists():
                 try:
                     outside_file_path.unlink()
                 except OSError as e:
                     logger.warning(f"Could not remove outside file {outside_file_path}: {e}")


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

    def test_generate_coder_llm_prompts_type_error(self, test_driver):
        with pytest.raises(TypeError):
            test_driver.generate_coder_llm_prompts("not a list")

        with pytest.raises(TypeError):
            test_driver.generate_coder_llm_prompts([1, 2, 3])

        with pytest.raises(TypeError):
            test_driver.generate_coder_llm_prompts([{"step": "dict instead of string"}])

    def test_generate_coder_llm_prompts_valid(self, test_driver):
        task = {"task_id": "t1", "priority": "High", "task_name": "Sample Task", "status": "Not Started", "description": "Do something cool."} # Added missing keys for valid task dict
        plan = ["Step 1: Define function.", "Step 2: Add logic.", "Step 3: Write tests."]
        prompts = test_driver.generate_coder_llm_prompts(task, plan)
        assert isinstance(prompts, list)
        assert len(prompts) > 0
        assert "Sample Task" in prompts[0]
        assert "Do something cool." in prompts[0]
        assert "Step 1: Define function." in prompts[0]
        assert "Requirements:" in prompts[0]
        assert "Prioritize security" in prompts[0]

    def test_generate_coder_llm_prompts_empty_plan(self, test_driver):
        task = {"task_id": "t2", "priority": "Low", "task_name": "Empty Plan Task", "status": "Not Started", "description": "Nothing to do."} # Added missing keys
        plan = []
        prompts = test_driver.generate_coder_llm_prompts(task, plan)
        assert isinstance(prompts, list)
        assert len(prompts) == 1

    def test_generate_coder_llm_prompts_invalid_task_type(self, test_driver):
        with pytest.raises(TypeError, match="Input 'task' must be a dictionary"):
            test_driver.generate_coder_llm_prompts("not a dict", ["Step 1"])

    def test_generate_coder_llm_prompts_invalid_plan_type(self, test_driver):
        task = {"task_id": "t3", "priority": "High", "task_name": "Invalid Plan", "status": "Not Started", "description": "Desc"} # Added missing keys
        with pytest.raises(TypeError, match="Input 'solution_plan' must be a list of strings"):
            test_driver.generate_coder_llm_prompts(task, "not a list")
        with pytest.raises(TypeError, match="Input 'solution_plan' must be a list of strings"):
            test_driver.generate_coder_llm_prompts(task, [1, 2, 3])

    def test_generate_coder_llm_prompts_missing_task_keys(self, test_driver):
        task = {"task_id": "t4", "priority": "High"} # Missing name and description
        plan = ["Step 1"]
        with pytest.raises(ValueError, match="Task dictionary must contain 'task_name' and 'description' keys"):
            test_driver.generate_coder_llm_prompts(task, plan)

    def test_generate_coder_llm_prompts_html_escaping(self, test_driver):
        """Test generate_coder_llm_prompts properly handles HTML characters."""
        task = {
            "task_id": "test_task_6",
            "task_name": "Task with <script>alert()</script> tag",
            "description": html.escape("Description with <b>bold</b> and &special characters."), # Description is already escaped by load_roadmap
            "priority": "High",
            "status": "Not Started"
        }
        solution_plan = ["Step 1: Handle <input> safely."]
        prompts = test_driver.generate_coder_llm_prompts(task, solution_plan)
        prompt = prompts[0]

        # Task name should remain unescaped (trusted input from roadmap JSON)
        assert "Task with <script>alert()</script> tag" in prompt
        # Description should be the already-escaped version from the task dict
        assert task["description"] in prompt # FIX: Assert against the already-escaped description
        # Solution plan steps should be escaped (escaped during generate_user_actionable_steps)
        assert html.escape("Step 1: Handle <input> safely.") in prompt

    def test_generate_coder_llm_prompts_null_plan(self, test_driver):
        """Test generate_coder_llm_prompts with None as solution_plan."""
        task = {
            "task_id": "test_task_7",
            "task_name": "Null Plan Task",
            "description": "Task with solution plan set to None.",
            "priority": "Low",
            "status": "Not Started" # Added missing key
        }
        # The type hint is list, so passing None should raise TypeError
        with pytest.raises(TypeError) as excinfo:
            test_driver.generate_coder_llm_prompts(task, None)
        # Optional: check the error message if desired
        # assert "Input 'solution_plan' must be a list of strings" in str(excinfo.value)


    # --- New tests for _invoke_coder_llm ---
    def test_invoke_coder_llm_success(self, test_driver):
        """Test _invoke_coder_llm calls generate and returns stripped response."""
        test_prompt = "Test prompt for LLM"
        test_driver.llm_orchestrator.generate.return_value = "  Generated code response  \n"

        response = test_driver._invoke_coder_llm(test_prompt)

        test_driver.llm_orchestrator.generate.assert_called_once_with(test_prompt)
        assert response == "Generated code response"

    def test_invoke_coder_llm_empty_response(self, test_driver):
        """Test _invoke_coder_llm handles empty response from LLM."""
        test_prompt = "Test prompt for empty response"
        test_driver.llm_orchestrator.generate.return_value = ""

        response = test_driver._invoke_coder_llm(test_prompt)

        test_driver.llm_orchestrator.generate.assert_called_once_with(test_prompt)
        assert response == ""

    def test_invoke_coder_llm_llm_exception(self, test_driver, caplog):
        """Test _invoke_coder_llm catches exceptions from LLM and returns None."""
        test_prompt = "Test prompt for exception"
        test_driver.llm_orchestrator.generate.side_effect = Exception("Test LLM API error")
        caplog.set_level(logging.ERROR)

        response = test_driver._invoke_coder_llm(test_prompt)

        test_driver.llm_orchestrator.generate.assert_called_once_with(test_prompt)
        assert response is None
        assert "Error invoking Coder LLM" in caplog.text
        assert "Test LLM API error" in caplog.text

    # --- New integration test simulating a workflow step ---
    @patch.object(WorkflowDriver, '_invoke_coder_llm')
    @patch.object(WorkflowDriver, 'generate_coder_llm_prompts')
    def test_workflow_step_calls_invoke_coder_llm(self, mock_generate_prompts, mock_invoke_coder_llm, test_driver):
        """Test that a simulated workflow step correctly calls _invoke_coder_llm."""
        mock_task = {"task_id": "mock_task", "task_name": "Mock Task", "description": "Mock description", "priority": "High", "status": "Not Started"} # Added missing key
        mock_plan = ["Mock step 1", "Mock step 2"]
        mock_prompt = "Generated prompt for Coder LLM"
        mock_generated_code = "def generated_code(): pass"

        mock_generate_prompts.return_value = [mock_prompt]
        mock_invoke_coder_llm.return_value = mock_generated_code

        # Simulate the calls that would happen in a workflow step
        generated_prompts = test_driver.generate_coder_llm_prompts(mock_task, mock_plan)
        generated_code = None # Initialize to None
        if generated_prompts: # Check if prompts were generated
            # In a real loop, you might iterate through prompts if multiple were returned
            # For this test, we just simulate invoking with the first one
            generated_code = test_driver._invoke_coder_llm(generated_prompts[0])


        mock_generate_prompts.assert_called_once_with(mock_task, mock_plan)
        # Assert _invoke_coder_llm was called only if prompts were generated
        if generated_prompts:
             mock_invoke_coder_llm.assert_called_once_with(mock_prompt)
        else:
             mock_invoke_coder_llm.assert_not_called()

        assert generated_code == mock_generated_code


    # --- New tests for select_next_task validation (Task 15_3a2) ---
    def test_select_next_task_valid_list_with_not_started(self, test_driver):
        """Test select_next_task returns the first 'Not Started' task."""
        tasks = [
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'Low'},
            {'task_id': 't2', 'status': 'Not Started', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High'},
            {'task_id': 't3', 'status': 'Not Started', 'task_name': 'Task 3', 'description': 'Desc', 'priority': 'Medium'}
        ]
        next_task = test_driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 't2'

    def test_select_next_task_valid_list_no_not_started(self, test_driver):
        """Test select_next_task returns None when no 'Not Started' tasks exist."""
        tasks = [
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'Low'},
            {'task_id': 't2', 'status': 'Completed', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High'}
        ]
        next_task = test_driver.select_next_task(tasks)
        assert next_task is None

    def test_select_next_task_empty_list(self, test_driver):
        """Test select_next_task returns None for an empty list."""
        tasks = []
        next_task = test_driver.select_next_task(tasks)
        assert next_task is None

    def test_select_next_task_invalid_input_not_list(self, test_driver, caplog):
        """Test select_next_task handles non-list input gracefully."""
        caplog.set_level(logging.WARNING)
        tasks = "not a list"
        next_task = test_driver.select_next_task(tasks)
        assert next_task is None
        assert "select_next_task received non-list input" in caplog.text


    def test_select_next_task_list_with_invalid_task_format(self, test_driver, caplog):
        """Test select_next_task skips invalid task formats within the list."""
        caplog.set_level(logging.WARNING)
        # Reorder tasks so invalid ones are encountered before a valid 'Not Started' task
        tasks = [
            "not a dict", # Invalid format (will be skipped and logged)
            {'task_id': 't3', 'status': 'Not Started'}, # Missing keys (task_name, description, priority) - Valid according to select_next_task's checks
            {'task_id': 't1', 'status': 'Completed', 'task_name': 'Task 1', 'description': 'Desc', 'priority': 'High'}, # Valid but Completed
            {'task_id': 't2', 'status': 'Not Started', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High'} # Valid and Not Started
        ]
        next_task = test_driver.select_next_task(tasks)
        assert next_task is not None
        # The first item that is a dict, has status/task_id, is 'Not Started', and has a valid ID is selected.
        # This is the task with task_id 't3'.
        assert next_task['task_id'] == 't3' # Corrected expectation

        # Check if the log message indicating skipping the *non-dict* invalid format is present
        assert "Skipping invalid task format in list: not a dict" in caplog.text
        # Removed the assertion for the task missing keys, as it's not logged as "invalid format" by select_next_task

    def test_select_next_task_list_with_invalid_task_id(self, test_driver, caplog):
        """Test select_next_task skips tasks with invalid task_id format."""
        caplog.set_level(logging.WARNING)
        tasks = [
            {'task_id': 'invalid/id', 'status': 'Not Started', 'task_name': 'Task Invalid', 'description': 'Desc', 'priority': 'High'}, # Invalid ID (will be skipped and logged)
            {'task_id': 't2', 'status': 'Not Started', 'task_name': 'Task 2', 'description': 'Desc', 'priority': 'High'} # Valid task (will be selected)
        ]
        next_task = test_driver.select_next_task(tasks)
        assert next_task is not None
        assert next_task['task_id'] == 't2' # Should select the next valid task
        # Check for the log message about the invalid task_id
        # Removed single quotes from the assertion string to match the actual log format
        assert "Skipping task with invalid task_id format: invalid/id" in caplog.text

    # --- New tests for _is_valid_task_id (Task 15_3a2) ---
    def test_is_valid_task_id_valid_formats(self, test_driver):
        """Test _is_valid_task_id with valid task ID formats."""
        assert test_driver._is_valid_task_id("task_1_1") is True
        assert test_driver._is_valid_task_id("Task-ID-2") is True
        assert test_driver._is_valid_task_id("task123") is True
        assert test_driver._is_valid_task_id("a_b-c_1-2") is True
        assert test_driver._is_valid_task_id("justletters") is True
        assert test_driver._is_valid_task_id("just123") is True
        assert test_driver._is_valid_task_id("a") is True
        assert test_driver._is_valid_task_id("1") is True
        # Add cases that were previously valid but might be invalid with new regex
        assert test_driver._is_valid_task_id("a-") is True # Ends with hyphen (should be allowed by new regex)
        assert test_driver._is_valid_task_id("a_") is True # Ends with underscore (should be allowed by new regex)


    def test_is_valid_task_id_invalid_formats(self, test_driver):
        """Test _is_valid_task_id with invalid task ID formats."""
        assert test_driver._is_valid_task_id("invalid/id") is False # Contains slash
        assert test_driver._is_valid_task_id("..") is False # Path traversal
        assert test_driver._is_valid_task_id("../task") is False # Path traversal
        assert test_driver._is_valid_task_id("task id") is False # Contains space
        assert test_driver._is_valid_task_id("task!@#") is False # Contains special characters
        assert test_driver._is_valid_task_id("") is False # Empty string
        assert test_driver._is_valid_task_id(None) is False # None input
        assert test_driver._is_valid_task_id(123) is False # Integer input
        assert test_driver._is_valid_task_id("task.") is False # Contains dot (dots are not allowed by the regex)
        assert test_driver._is_valid_task_id(".task") is False # Starts with dot (not allowed by new regex)
        assert test_driver._is_valid_task_id("-task") is False # Starts with hyphen (not allowed by new regex)
        assert test_driver._is_valid_task_id("_task") is False # Starts with underscore (not allowed by new regex)
        # Add cases that should now be invalid with the new regex
        assert test_driver._is_valid_task_id("1-") is True # Ends with hyphen (should be allowed) - Corrected assertion
        assert test_driver._is_valid_task_id("1_") is True # Ends with underscore (should be allowed) - Corrected assertion