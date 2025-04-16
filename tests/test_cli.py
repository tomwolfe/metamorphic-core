# tests/test_cli.py
import pytest
import argparse
import os
import sys
from unittest.mock import patch, MagicMock
import logging # Added logging import
from src.cli.main import cli_entry_point
from src.core.automation.workflow_driver import WorkflowDriver, Context

@pytest.fixture
def mock_workflow_driver():
    # Patch the WorkflowDriver class within the src.cli.main module where it's imported and used
    with patch('src.cli.main.WorkflowDriver') as mock_driver:
        # Configure the mock instance that will be returned when WorkflowDriver is called
        mock_instance = mock_driver.return_value
        # Set default return values for methods that might be called
        mock_instance.load_roadmap.return_value = []
        mock_instance.select_next_task.return_value = None
        yield mock_driver # Yield the mock class itself

class TestCLIArguments:
    """Test suite for CLI argument parsing and validation."""

    def test_cli_help_message(self, capsys):
        """Test --help flag displays usage information."""
        with patch('sys.argv', ['main.py', '--help']), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        captured = capsys.readouterr()
        assert "usage:" in captured.out
        assert "--roadmap" in captured.out
        assert "--output-dir" in captured.out

    def test_cli_version_message(self, capsys):
        """Test --version flag displays correct version string."""
        with patch('sys.argv', ['main.py', '--version']), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        captured = capsys.readouterr()
        assert "Metamorphic CLI v0.1.0-alpha" in captured.out

    @patch('src.cli.main.WorkflowDriver')
    @patch('src.cli.main._validate_output_dir')
    @patch('src.cli.main._validate_roadmap_path')
    def test_cli_default_args(self, mock_validate_roadmap, mock_validate_output, mock_driver, capsys, tmp_path):
        """Test CLI with default arguments."""
        # Create absolute path for roadmap file
        roadmap_path = tmp_path / "ROADMAP.json"
        roadmap_path.write_text('{"tasks":[]}')
        output_path = tmp_path / "output"
        # Configure mocks to return absolute paths
        mock_validate_roadmap.return_value = str(roadmap_path)
        mock_validate_output.return_value = str(output_path)
    
        # Configure the mock instance
        mock_instance = mock_driver.return_value
        mock_instance.load_roadmap.return_value = []
    
        with patch('sys.argv', ['main.py']):
            cli_entry_point()
        
        captured = capsys.readouterr()
        assert f"Using roadmap: {str(roadmap_path)}" in captured.out
        assert f"Using output directory: {str(output_path)}" in captured.out
        mock_instance.load_roadmap.assert_called_once_with(str(roadmap_path))

    @patch('src.cli.main.WorkflowDriver')
    @patch('src.cli.main._validate_output_dir')
    @patch('src.cli.main._validate_roadmap_path')
    def test_cli_custom_args_exist(self, mock_validate_roadmap, mock_validate_output, mock_driver, capsys, tmp_path):
        """Test CLI with custom valid arguments."""
        # Create custom roadmap file
        custom_roadmap = tmp_path / "custom_roadmap.json"
        custom_roadmap.write_text('{"tasks":[]}')
        custom_output = tmp_path / "custom_output"
        os.makedirs(custom_output, exist_ok=True)
    
        # Configure mocks to return absolute paths
        mock_validate_roadmap.return_value = str(custom_roadmap)
        mock_validate_output.return_value = str(custom_output)
    
        # Configure the mock instance
        mock_instance = mock_driver.return_value
        mock_instance.load_roadmap.return_value = []
    
        with patch('sys.argv', ['main.py', '--roadmap', 'custom_roadmap.json', '--output-dir', 'custom_output']):
            cli_entry_point()
        
        captured = capsys.readouterr()
        assert f"Using roadmap: {str(custom_roadmap)}" in captured.out
        assert f"Using output directory: {str(custom_output)}" in captured.out
        mock_instance.load_roadmap.assert_called_once_with(str(custom_roadmap))

    def test_cli_roadmap_not_exist(self):
        """Test CLI with non-existent roadmap file."""
        with patch('sys.argv', ['main.py', '--roadmap', 'nonexistent.json']), \
             patch('src.cli.main._validate_roadmap_path', side_effect=argparse.ArgumentTypeError("File does not exist")), \
             pytest.raises(SystemExit):
            cli_entry_point()

    def test_cli_output_dir_not_exist(self):
        """Test CLI with non-existent output directory."""
        with patch('sys.argv', ['main.py', '--output-dir', 'nonexistent_dir']), \
             patch('src.cli.main._validate_output_dir', side_effect=argparse.ArgumentTypeError("Directory does not exist")), \
             pytest.raises(SystemExit):
            cli_entry_point()

    def test_cli_output_dir_is_file(self):
        """Test CLI when output directory path is actually a file."""
        with patch('sys.argv', ['main.py', '--output-dir', 'output_is_file']), \
             patch('src.cli.main._validate_output_dir', side_effect=argparse.ArgumentTypeError("Path is not a directory")), \
             pytest.raises(SystemExit):
            cli_entry_point()

        # Use the fixture for workflow tests
    @patch('src.cli.main._validate_output_dir', return_value='./output')
    @patch('src.cli.main._validate_roadmap_path', return_value='ROADMAP.json')
    def test_cli_workflow_task_selected(self, mock_validate_roadmap, mock_validate_output, caplog, mock_workflow_driver):
        """Test CLI workflow when a task is selected."""
        caplog.set_level(logging.INFO)
        # Get the mock instance returned by the fixture's patch
        mock_instance = mock_workflow_driver.return_value
        mock_instance.load_roadmap.return_value = [{'task_id': 't1', 'status': 'Not Started', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High'}]
        # Configure select_next_task for this specific test case
        mock_instance.select_next_task.return_value = {'task_id': 't1', 'task_name': 'Mock Task'}

        with patch('sys.argv', ['main.py']):
            cli_entry_point()

        mock_instance.load_roadmap.assert_called_once_with('ROADMAP.json')
        mock_instance.select_next_task.assert_called_once()
        assert "Next task selected: ID=t1, Name=Mock Task" in caplog.text

    @patch('src.cli.main._validate_output_dir', return_value='./output')
    @patch('src.cli.main._validate_roadmap_path', return_value='ROADMAP.json')
    def test_cli_workflow_no_task(self, mock_validate_roadmap, mock_validate_output, caplog, mock_workflow_driver):
        """Test CLI workflow when no task is available."""
        caplog.set_level(logging.INFO)
        # Get the mock instance returned by the fixture's patch
        mock_instance = mock_workflow_driver.return_value
        mock_instance.load_roadmap.return_value = [{'task_id': 't1', 'status': 'Completed', 'task_name': 'Done Task', 'description': 'Desc', 'priority': 'High'}] # No 'Not Started' tasks
        # select_next_task already defaults to None from fixture setup, but can be explicit:
        mock_instance.select_next_task.return_value = None

        with patch('sys.argv', ['main.py']):
            cli_entry_point()

        mock_instance.load_roadmap.assert_called_once_with('ROADMAP.json')
        mock_instance.select_next_task.assert_called_once()
        assert "No tasks available in 'Not Started' status." in caplog.text

    @patch('src.cli.main._validate_output_dir', return_value='./output')
    @patch('src.cli.main._validate_roadmap_path', return_value='ROADMAP.json')
    def test_cli_workflow_exception(self, mock_validate_roadmap, mock_validate_output, caplog, mock_workflow_driver):
        """Test CLI workflow when WorkflowDriver raises an exception."""
        caplog.set_level(logging.ERROR)
        # Get the mock instance returned by the fixture's patch
        mock_instance = mock_workflow_driver.return_value
        mock_instance.load_roadmap.return_value = [{'task_id': 't1', 'status': 'Not Started', 'task_name': 'Mock Task', 'description': 'Desc', 'priority': 'High'}]
        # Configure select_next_task to raise an exception for this test
        mock_instance.select_next_task.side_effect = Exception("Test Error")

        with patch('sys.argv', ['main.py']):
            cli_entry_point()

        mock_instance.load_roadmap.assert_called_once_with('ROADMAP.json')
        mock_instance.select_next_task.assert_called_once()
        assert "An error occurred during workflow execution: Test Error" in caplog.text