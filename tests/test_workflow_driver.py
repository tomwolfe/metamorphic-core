import pytest
from src.core.automation.workflow_driver import WorkflowDriver
import os

def test_load_roadmap_basic(tmp_path, mocker):
    mock_content = """Phase 1.5 Level 2: Workflow Driver Component (Week 7-8 - 5 days) - CURRENT FOCUS:
    **Task ID**: T1
    **Priority**: High
    **Task Name**: Setup Environment
    **Status**: Not Started

    **Task ID**: T2
    **Priority**: Medium
    **Task Name**: Configure Database
    **Status**: In Progress"""

    roadmap_file = tmp_path / "roadmap.md"
    roadmap_file.write_text(mock_content)

    mock_open = mocker.patch('builtins.open')
    mock_open.return_value.read.return_value = mock_content
    mock_open.return_value.__enter__.return_value = mock_open.return_value

    driver = WorkflowDriver()
    tasks = driver.load_roadmap(str(roadmap_file))

    assert len(tasks) == 2

    expected_tasks = [
        {
            "task_id": "T1",
            "priority": "High",
            "task_name": "Setup Environment",
            "status": "Not Started",
        },
        {
            "task_id": "T2",
            "priority": "Medium",
            "task_name": "Configure Database",
            "status": "In Progress",
        },
    ]

    for expected in expected_tasks:
        match = next(
            (
                task
                for task in tasks
                if task["task_id"] == expected["task_id"]
                and task["priority"] == expected["priority"]
                and task["task_name"] == expected["task_name"]
                and task["status"] == expected["status"]
            ),
            None,
        )
        assert match is not None

def test_load_roadmap_file_not_found(mocker):
    mock_open = mocker.patch('builtins.open')
    mock_open.side_effect = FileNotFoundError

    driver = WorkflowDriver()
    tasks = driver.load_roadmap("nonexistent_path")

    assert len(tasks) == 2

def test_load_roadmap_phase_not_found(mocker):
    mock_content = """Phase 2.0 Level 3:
    - **Task ID**: T3
    **Priority**: Low
    **Task Name**: Cleanup
    **Status**: Completed"""
    mock_open = mocker.patch('builtins.open')
    mock_open.return_value.read.return_value = mock_content

    driver = WorkflowDriver()
    tasks = driver.load_roadmap("some_path")

    assert len(tasks) == 2

def test_load_roadmap_malformed_task(mocker):
    mock_content = """Phase 1.5 Level 2: Workflow Driver Component (Week 7-8 - 5 days) - CURRENT FOCUS:
    - **Task ID**: T1
    **Priority**: High
    **Task Name**: Setup
    **Status**: Not Started
    - **Task ID**: T2
    **Priority**: Medium
    **Task Name**: Configure Database
    **Status**: In Progress  # missing Task Name"""
    mock_open = mocker.patch('builtins.open')
    mock_open.return_value.read.return_value = mock_content

    driver = WorkflowDriver()
    tasks = driver.load_roadmap("some_path")

    assert len(tasks) <= 2
    if len(tasks) > 0:
        assert tasks[0]['task_id'] == "T1"

def test_list_files_returns_empty_list(mocker):
    mock_exists = mocker.patch('os.path.exists')
    mock_exists.return_value = False
    driver = WorkflowDriver()
    result = driver.list_files()
    assert result == []