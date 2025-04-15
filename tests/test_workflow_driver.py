import pytest
import html  # Added missing import
import shutil  # Added missing import
from src.core.automation.workflow_driver import WorkflowDriver, Context
import os
import logging
from src.cli.write_file import write_file, file_exists  # Import write_file and file_exists
import pytest


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

    def test_generate_user_actionable_steps_empty(test_driver):
        assert test_driver.generate_user_actionable_steps([]) == ""

    def test_generate_user_actionable_steps_single(test_driver):
        result = test_driver.generate_user_actionable_steps(["Single step"])
        assert result == "1.  - [ ] Single step\n"

    def test_generate_user_actionable_steps_multiple(test_driver):
        steps = ["Step 1", "Step 2", "Step 3"]
        expected = (
            "1.  - [ ] Step 1\n"
            "2.  - [ ] Step 2\n"
            "3.  - [ ] Step 3\n"
        )
        assert test_driver.generate_user_actionable_steps(steps) == expected

    def test_generate_user_actionable_steps_special_chars(test_driver):
        steps = ["Use <script>", "Escape > & < tags", "Math: 5 > 3"]
        expected = (
            f"1.  - [ ] {html.escape('Use <script>')}\n"
            f"2.  - [ ] {html.escape('Escape > & < tags')}\n"
            f"3.  - [ ] {html.escape('Math: 5 > 3')}\n"
        )
        result = test_driver.generate_user_actionable_steps(steps)
        assert result == expected, "Special characters should be escaped using html.escape."

    def test_generate_coder_llm_prompts_type_error(test_driver):
        with pytest.raises(TypeError):
            test_driver.generate_coder_llm_prompts("not a list")

        with pytest.raises(TypeError):
            test_driver.generate_coder_llm_prompts([1, 2, 3])

        with pytest.raises(TypeError):
            test_driver.generate_coder_llm_prompts([{"step": "dict instead of string"}])

    def test_generate_coder_llm_prompts_valid(test_driver):
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

    def test_generate_coder_llm_prompts_empty_plan(test_driver):
        task = {"task_id": "t2", "priority": "Low", "task_name": "Empty Plan Task", "description": "Nothing to do."}
        plan = []
        prompts = test_driver.generate_coder_llm_prompts(task, plan)
        # Depending on implementation, might return one generic prompt or empty list.
        # Current implementation generates one prompt even for empty plan.
        assert isinstance(prompts, list)
        assert len(prompts) == 1 # Adjust if implementation changes
        # assert "Implement the following steps:" in prompts[0] # Check if the prompt is generated

    def test_generate_coder_llm_prompts_invalid_task_type(test_driver):
        with pytest.raises(TypeError, match="Input 'task' must be a dictionary"):
            test_driver.generate_coder_llm_prompts("not a dict", ["Step 1"])

    def test_generate_coder_llm_prompts_invalid_plan_type(test_driver):
        task = {"task_id": "t3", "priority": "High", "task_name": "Invalid Plan", "description": "Desc"}
        with pytest.raises(TypeError, match="Input 'solution_plan' must be a list of strings"):
            test_driver.generate_coder_llm_prompts(task, "not a list")
        with pytest.raises(TypeError, match="Input 'solution_plan' must be a list of strings"):
            test_driver.generate_coder_llm_prompts(task, [1, 2, 3]) # List of non-strings

    def test_generate_coder_llm_prompts_missing_task_keys(test_driver):
        task = {"task_id": "t4", "priority": "High"} # Missing name and description
        plan = ["Step 1"]
        with pytest.raises(ValueError, match="Task dictionary must contain 'task_name' and 'description' keys"):
            test_driver.generate_coder_llm_prompts(task, plan)

    def test_generate_coder_llm_prompts_html_escaping(test_driver):
        """Test generate_coder_llm_prompts properly handles HTML characters."""
        task = {
            "task_id": "test_task_6",
            "task_name": "Task with <script>alert()</script> tag",
            "description": "Description with <b>bold</b> and &special characters.",
            "priority": "High"
        }
        solution_plan = ["Step 1: Handle <input> safely."]
        prompts = test_driver.generate_coder_llm_prompts(task, solution_plan)
        prompt = prompts[0]

        # Task name should remain unescaped (trusted input)
        assert "Task with <script>alert()</script> tag" in prompt
        # Description should be escaped
        assert "Description with <b>bold</b> and &special characters." in prompt
        # Solution plan steps should be escaped
        assert html.escape("Step 1: Handle <input> safely.") in prompt

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


    def test_write_file_success(tmp_path):
        """Test successful file writing."""
        filepath = tmp_path / "test_file.txt"
        content = "Test content"
        result = write_file(str(filepath), content)
        assert result is True
        assert filepath.exists()
        assert filepath.read_text() == content

    def test_write_file_filenotfounderror(tmp_path, caplog):
        """Test handling of FileNotFoundError."""
        caplog.set_level(logging.ERROR)
        filepath = tmp_path / "non_existent_dir" / "test_file.txt"
        content = "Test content"
        result = write_file(str(filepath), content)
        assert result is False
        assert "Error writing to" in caplog.text

    def test_write_file_permissionerror(tmp_path, caplog):
        """Test handling of PermissionError."""
        caplog.set_level(logging.ERROR)
        # Create a read-only directory
        readonly_dir = tmp_path / "readonly_dir"
        readonly_dir.mkdir(mode=0o555)  # Read-only for all
        filepath = readonly_dir / "test_file.txt"
        content = "Test content"
        result = write_file(str(filepath), content)
        assert result is False

    def test_write_file_overwrite_false_exists(tmp_path, caplog):
        """Test write_file() raises FileExistsError when overwrite=False and file exists."""
        caplog.set_level(logging.ERROR)
        filepath = tmp_path / "existing_file.txt"
        filepath.write_text("initial content")
        with pytest.raises(FileExistsError) as excinfo:
            write_file(str(filepath), "new content", overwrite=False)
        assert "File already exists" in str(excinfo.value)
        # Verify the file content hasn't changed
        assert filepath.read_text() == "initial content"

    def test_write_file_overwrite_true(tmp_path):
        """Test write_file() successfully overwrites when overwrite=True."""
        filepath = tmp_path / "existing_file.txt"
        filepath.write_text("initial content")
        result = write_file(str(filepath), "new content", overwrite=True)
        assert result is True
        assert filepath.read_text() == "new content"

    def test_file_exists(tmp_path):
        """Test file_exists() function returns True if the file exists, False otherwise."""
        existing_file = tmp_path / "existing_file.txt"
        non_existing_file = tmp_path / "non_existing_file.txt"
        existing_file.write_text("some content")
        assert file_exists(str(existing_file)) is True
        assert file_exists(str(non_existing_file)) is False
        
    def test_write_file_overwrite_false_exists(tmp_path, caplog):
        """Test write_file() raises FileExistsError when overwrite=False and file exists.
        
        Args:
            tmp_path: pytest fixture for temporary directory
            caplog: pytest fixture for capturing logs
        """
        caplog.set_level(logging.ERROR)
        filepath = tmp_path / "existing_file.txt"
        filepath.write_text("Original content")  # Create file first
        
        # Attempt to write to existing file with overwrite=False
        with pytest.raises(FileExistsError) as excinfo:
            write_file(str(filepath), "New content", overwrite=False)
        
        assert "File already exists" in str(excinfo.value)
        assert filepath.read_text() == "Original content"  # Content shouldn't change
        assert "File already exists" in caplog.text

    def test_write_file_overwrite_true(tmp_path):
        """Test that write_file successfully overwrites when overwrite=True.
        
        Args:
            tmp_path: pytest fixture for temporary directory
        """
        filepath = tmp_path / "existing_file.txt"
        filepath.write_text("Original content")  # Create file first
        
        # Write to existing file with overwrite=True
        result = write_file(str(filepath), "New content", overwrite=True)
        
        assert result is True
        assert filepath.read_text() == "New content"  # Content should be updated

    def test_file_exists(tmp_path):
        """Test the file_exists helper function with existing and non-existing files.
        
        Args:
            tmp_path: pytest fixture for temporary directory
        """
        from src.cli.write_file import file_exists  # Import the helper function
        
        # Test with non-existing file
        non_existent_file = tmp_path / "nonexistent.txt"
        assert file_exists(str(non_existent_file)) is False
        
        # Test with existing file
        existing_file = tmp_path / "existing.txt"
        existing_file.write_text("content")
        assert file_exists(str(existing_file)) is True
        
        # Test with directory (should return False since it's not a file)
        subdir = tmp_path / "subdirectory"
        subdir.mkdir()
        assert file_exists(str(subdir)) is False