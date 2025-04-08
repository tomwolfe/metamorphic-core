import pytest
from src.core.automation.workflow_driver import WorkflowDriver
import os
from unittest.mock import patch, mock_open
import logging

# Set up logging for tests
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@pytest.fixture
def test_driver():
    """Fixture to create a WorkflowDriver instance."""
    return WorkflowDriver()

def create_mock_roadmap_file(content, tmp_path):
    """Helper to create a temporary ROADMAP.md file with specified content."""
    roadmap_file = tmp_path / "ROADMAP.md"
    roadmap_file.write_text(content)
    return str(roadmap_file)

def test_load_roadmap_parses_valid_file(test_driver, tmp_path):
    """Test that load_roadmap correctly parses a valid ROADMAP.md file."""
    roadmap_content = """
*   **Task ID**: T1
    *   **Priority**: High
    *   **Task Name**: Setup Environment
    *   **Status**: Not Started

*   **Task ID**: T2
    *   **Priority**: Medium
    *   **Task Name**: Configure Database
    *   **Status**: In Progress

*   **Task ID**: T3
    *   **Priority**: Low
    *   **Task Name**: Implement Unit Tests.  This is a very long task name to ensure the parsing works correctly even with lots of text. And even more text. AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
    *   **Status**: Completed
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 3
    assert tasks[0]["task_id"] == "T1"
    assert tasks[0]["priority"] == "High"
    assert tasks[0]["task_name"] == "Setup Environment"
    assert tasks[0]["status"] == "Not Started"
    assert tasks[1]["task_id"] == "T2"
    assert tasks[1]["priority"] == "Medium"
    assert tasks[1]["task_name"] == "Configure Database"
    assert tasks[1]["status"] == "In Progress"
    assert tasks[2]["task_name"].startswith("Implement Unit Tests")

def test_load_roadmap_handles_missing_file(test_driver, caplog):
    """Test that load_roadmap gracefully handles a missing ROADMAP.md file."""
    caplog.set_level(logging.ERROR)
    tasks = test_driver.load_roadmap("nonexistent_file.md")
    assert len(tasks) == 0
    assert "ROADMAP.md file not found" in caplog.text

def test_load_roadmap_handles_parsing_errors(test_driver, tmp_path, caplog):
    """Test that load_roadmap handles improperly-formatted ROADMAP.md content."""
    caplog.set_level(logging.ERROR)
    roadmap_content = """
*   **Task ID**: T1
    *   **Priority**: High
    *   **Task Name**: Missing Status

*   **Task ID**: T2
    *   **Priority**: Medium
    *   **Status**: This is invalid
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 2
    assert tasks[0]["task_id"] == "T1"
    assert tasks[0]["priority"] == "High"
    assert tasks[0]["task_name"] == "Missing Status"

def test_load_roadmap_handles_empty_file(test_driver, tmp_path):
    """Test that load_roadmap handles an empty ROADMAP.md file."""
    roadmap_file = create_mock_roadmap_file("", tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 0

def test_load_roadmap_handles_invalid_task_id(test_driver, tmp_path):
    """Test that load_roadmap handles a ROADMAP.md file with a malformed Task ID."""
    roadmap_content = """
*   **Task ID**: ../etc/passwd
    *   **Priority**: High
    *   **Task Name**: Setup Environment
    *   **Status**: Not Started
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 1
    assert tasks[0]["task_id"] == "../etc/passwd"

def test_load_roadmap_handles_long_task_content(test_driver, tmp_path):
    """Test that load_roadmap handles very long task content without errors."""
    long_name = "A" * 200  # Create a long task name
    roadmap_content = f"""
*   **Task ID**: LongTask
    *   **Priority**: High
    *   **Task Name**: {long_name}
    *   **Status**: Not Started
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 1
    assert tasks[0]["task_name"] == long_name

def test_load_roadmap_handles_various_spacing(test_driver, tmp_path):
    """Test that load_roadmap handles inconsistent spacing in the roadmap file."""
    roadmap_content = """
   * **Task ID**:SpacedID
     *  **Priority**: High
*       **Task Name**:   Spaced Name
    *  **Status**  :  Spaced Status
    """
    roadmap_file = create_mock_roadmap_file(roadmap_content, tmp_path)
    tasks = test_driver.load_roadmap(roadmap_file)
    assert len(tasks) == 1
    assert tasks[0]["task_id"] == "SpacedID"
    assert tasks[0]["priority"] == "High"
    assert tasks[0]["task_name"] == "Spaced Name"
    assert tasks[0]["status"] == "Spaced Status"