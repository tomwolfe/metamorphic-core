# tests/test_cli.py
import pytest
import argparse
import os
import sys
import json # Added json import
import requests # Added requests import
from unittest.mock import patch, MagicMock
import logging # Added logging import
from src.cli.main import cli_entry_point
from src.core.automation.workflow_driver import WorkflowDriver, Context # Keep Context import if needed elsewhere

# Set up logging for tests
# Use basicConfig only if no handlers are already configured
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@pytest.fixture
def mock_requests_post():
    """Fixture to mock requests.post."""
    with patch('requests.post') as mock_post:
        yield mock_post

@pytest.fixture
def mock_validate_paths():
    """Fixture to mock path validation helpers."""
    with patch('src.cli.main._validate_roadmap_path') as mock_roadmap_validator, \
         patch('src.cli.main._validate_output_dir') as mock_output_validator:
        # By default, make validators return the input path as if it's valid and absolute
        mock_roadmap_validator.side_effect = lambda x: os.path.abspath(x)
        mock_output_validator.side_effect = lambda x: os.path.abspath(x)
        yield {
            'roadmap': mock_roadmap_validator,
            'output': mock_output_validator
        }


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

    @patch('requests.post') # Mock requests.post as it will be called now
    @patch('src.cli.main._validate_output_dir')
    @patch('src.cli.main._validate_roadmap_path')
    def test_cli_default_args(self, mock_validate_roadmap, mock_validate_output, mock_post, capsys, tmp_path):
        """Test CLI with default arguments."""
        # Configure mocks to return absolute paths
        mock_validate_roadmap.return_value = os.path.abspath("ROADMAP.json")
        mock_validate_output.return_value = os.path.abspath("./output")

        # Mock the API call to return success
        mock_post.return_value = MagicMock(status_code=200, json=lambda: {"status": "success", "message": "Workflow initiated"}, text="{}")

        with patch('sys.argv', ['main.py']):
            cli_entry_point()

        captured = capsys.readouterr()
        assert f"Using roadmap: {os.path.abspath('ROADMAP.json')}" in captured.out
        assert f"Using output directory: {os.path.abspath('./output')}" in captured.out
        mock_validate_roadmap.assert_called_once_with("ROADMAP.json")
        mock_validate_output.assert_called_once_with("./output")
        # Verify the API call was made with the correct default payload
        mock_post.assert_called_once_with(
            "http://127.0.0.1:5000/genesis/drive_workflow",
            json={"roadmap_path": os.path.abspath("ROADMAP.json"), "output_dir": os.path.abspath("./output")}
        )


    @patch('requests.post') # Mock requests.post
    @patch('src.cli.main._validate_output_dir')
    @patch('src.cli.main._validate_roadmap_path')
    def test_cli_custom_args_exist(self, mock_validate_roadmap, mock_validate_output, mock_post, capsys, tmp_path):
        """Test CLI with custom valid arguments."""
        # Configure mocks to return absolute paths
        custom_roadmap_abs = os.path.abspath("custom_roadmap.json")
        custom_output_abs = os.path.abspath("custom_output")
        mock_validate_roadmap.return_value = custom_roadmap_abs
        mock_validate_output.return_value = custom_output_abs

        # Mock the API call to return success
        mock_post.return_value = MagicMock(status_code=200, json=lambda: {"status": "success", "message": "Workflow initiated"}, text="{}")

        with patch('sys.argv', ['main.py', '--roadmap', 'custom_roadmap.json', '--output-dir', 'custom_output']):
            cli_entry_point()

        captured = capsys.readouterr()
        assert f"Using roadmap: {custom_roadmap_abs}" in captured.out
        assert f"Using output directory: {custom_output_abs}" in captured.out
        mock_validate_roadmap.assert_called_once_with("custom_roadmap.json")
        mock_validate_output.assert_called_once_with("custom_output")
        # Verify the API call was made with the correct custom payload
        mock_post.assert_called_once_with(
            "http://127.0.0.1:5000/genesis/drive_workflow",
            json={"roadmap_path": custom_roadmap_abs, "output_dir": custom_output_abs}
        )


    @patch('requests.post') # Mock requests.post
    def test_cli_roadmap_not_exist(self, mock_post):
        """Test CLI with non-existent roadmap file."""
        with patch('sys.argv', ['main.py', '--roadmap', 'nonexistent.json']), \
             patch('src.cli.main._validate_roadmap_path', side_effect=argparse.ArgumentTypeError("File does not exist")), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        assert excinfo.value.code == 2 # argparse exits with 2 for argument errors
        mock_post.assert_not_called() # API should not be called

    @patch('requests.post') # Mock requests.post
    def test_cli_output_dir_not_exist(self, mock_post):
        """Test CLI with non-existent output directory."""
        with patch('sys.argv', ['main.py', '--output-dir', 'nonexistent_dir']), \
             patch('src.cli.main._validate_output_dir', side_effect=argparse.ArgumentTypeError("Directory does not exist")), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        assert excinfo.value.code == 2 # argparse exits with 2 for argument errors
        mock_post.assert_not_called() # API should not be called

    @patch('requests.post') # Mock requests.post
    def test_cli_output_dir_is_file(self, mock_post):
        """Test CLI when output directory path is actually a file."""
        with patch('sys.argv', ['main.py', '--output-dir', 'output_is_file']), \
             patch('src.cli.main._validate_output_dir', side_effect=argparse.ArgumentTypeError("Path is not a directory")), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        assert excinfo.value.code == 2 # argparse exits with 2 for argument errors
        mock_post.assert_not_called() # API should not be called


# --- New tests for API Calling Logic (Task 1_6b) ---

# Note: The existing tests for WorkflowDriver interaction (load_roadmap, select_next_task)
# in the original test_cli.py are now obsolete as that logic has moved to the API/Driver.
# The tests below focus solely on the CLI's new responsibility: calling the API.

@patch('src.cli.main._validate_roadmap_path', return_value=os.path.abspath("ROADMAP.json"))
@patch('src.cli.main._validate_output_dir', return_value=os.path.abspath("./output"))
def test_cli_api_call_success(mock_validate_output, mock_validate_roadmap, mock_requests_post, caplog):
    """Test CLI successfully calls API and handles 200 response with JSON."""
    # Corrected: Set log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure the mock requests.post to return a successful response
    mock_requests_post.return_value = MagicMock(
        status_code=200,
        json=lambda: {"status": "success", "message": "Workflow initiated"},
        text='{"status": "success", "message": "Workflow initiated"}' # Include text for fallback
    )

    with patch('sys.argv', ['main.py']):
        cli_entry_point()

    # Verify requests.post was called once with the correct URL and payload
    mock_requests_post.assert_called_once_with(
        "http://127.0.0.1:5000/genesis/drive_workflow",
        json={"roadmap_path": os.path.abspath("ROADMAP.json"), "output_dir": os.path.abspath("./output")}
    )
    # Verify success message is logged
    assert "Calling API to initiate workflow at http://127.0.0.1:5000/genesis/drive_workflow..." in caplog.text
    assert "Workflow initiated successfully via API. Status: success, Message: Workflow initiated" in caplog.text
    # Ensure the script exited gracefully (implicitly, by not raising SystemExit with code 1)

@patch('src.cli.main._validate_roadmap_path', return_value=os.path.abspath("ROADMAP.json"))
@patch('src.cli.main._validate_output_dir', return_value=os.path.abspath("./output"))
def test_cli_api_call_success_non_json_200(mock_validate_output, mock_validate_roadmap, mock_requests_post, caplog):
    """Test CLI handles 200 response that is unexpectedly non-JSON."""
    # Corrected: Set log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure the mock requests.post to return a successful response but non-JSON body
    mock_requests_post.return_value = MagicMock(
        status_code=200,
        json=MagicMock(side_effect=json.JSONDecodeError("Not JSON", "{}", 0)), # Simulate JSON decode error
        text="OK" # Provide some text content
    )

    with patch('sys.argv', ['main.py']):
        cli_entry_point()

    # Verify requests.post was called
    mock_requests_post.assert_called_once()
    # Verify success message is logged, including the fallback text snippet
    assert "Calling API to initiate workflow at http://127.0.0.1:5000/genesis/drive_workflow..." in caplog.text
    assert "Workflow initiated successfully, but API returned non-JSON response. Status Code: 200. Response: OK" in caplog.text
    # Ensure the script exited gracefully

@patch('src.cli.main._validate_roadmap_path', return_value=os.path.abspath("ROADMAP.json"))
@patch('src.cli.main._validate_output_dir', return_value=os.path.abspath("./output"))
def test_cli_api_call_non_200_json_error(mock_validate_output, mock_validate_roadmap, mock_requests_post, caplog):
    """Test CLI handles non-200 status code with JSON error payload."""
    # Corrected: Set log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure the mock requests.post to return an error response with JSON
    mock_requests_post.return_value = MagicMock(
        status_code=400,
        json=lambda: {"status": "error", "message": "Invalid input provided"},
        text='{"status": "error", "message": "Invalid input provided"}' # Include text for fallback
    )

    with patch('sys.argv', ['main.py']), \
         pytest.raises(SystemExit) as excinfo:
        cli_entry_point()

    # Verify requests.post was called
    mock_requests_post.assert_called_once()
    # Verify error message is logged, including status code and JSON message
    assert "Calling API to initiate workflow at http://127.0.0.1:5000/genesis/drive_workflow..." in caplog.text
    assert "API returned error status code: 400. Message: Invalid input provided" in caplog.text
    # Verify script exited with code 1
    assert excinfo.value.code == 1

@patch('src.cli.main._validate_roadmap_path', return_value=os.path.abspath("ROADMAP.json"))
@patch('src.cli.main._validate_output_dir', return_value=os.path.abspath("./output"))
def test_cli_api_call_non_200_non_json(mock_validate_output, mock_validate_roadmap, mock_requests_post, caplog):
    """Test CLI handles non-200 status code with non-JSON response body."""
    # Corrected: Set log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure the mock requests.post to return an error response with plain text
    mock_requests_post.return_value = MagicMock(
        status_code=500,
        json=MagicMock(side_effect=json.JSONDecodeError("Not JSON", "{}", 0)), # Simulate JSON decode error
        text="Internal Server Error Details" # Provide plain text content
    )

    with patch('sys.argv', ['main.py']), \
         pytest.raises(SystemExit) as excinfo:
        cli_entry_point()

    # Verify requests.post was called
    mock_requests_post.assert_called_once()
    # Verify error message is logged, including status code and text snippet
    assert "Calling API to initiate workflow at http://127.0.0.1:5000/genesis/drive_workflow..." in caplog.text
    assert "API returned non-JSON response (Status 500): Internal Server Error Details..." in caplog.text
    # Verify script exited with code 1
    assert excinfo.value.code == 1

@patch('src.cli.main._validate_roadmap_path', return_value=os.path.abspath("ROADMAP.json"))
@patch('src.cli.main._validate_output_dir', return_value=os.path.abspath("./output"))
def test_cli_api_call_connection_error(mock_validate_output, mock_validate_roadmap, mock_requests_post, caplog):
    """Test CLI handles requests.exceptions.ConnectionError."""
    # Corrected: Set log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure the mock requests.post to raise ConnectionError
    mock_requests_post.side_effect = requests.exceptions.ConnectionError("Mock connection failed")

    with patch('sys.argv', ['main.py']), \
         pytest.raises(SystemExit) as excinfo:
        cli_entry_point()

    # Verify requests.post was called
    mock_requests_post.assert_called_once()
    # Verify error message is logged, including connection failure details
    assert "Calling API to initiate workflow at http://127.0.0.1:5000/genesis/drive_workflow..." in caplog.text
    assert "Failed to connect to API endpoint http://127.0.0.1:5000/genesis/drive_workflow: Mock connection failed" in caplog.text
    assert "Please ensure the Flask API server is running." in caplog.text
    # Verify script exited with code 1
    assert excinfo.value.code == 1

@patch('src.cli.main._validate_roadmap_path', return_value=os.path.abspath("ROADMAP.json"))
@patch('src.cli.main._validate_output_dir', return_value=os.path.abspath("./output"))
def test_cli_api_call_generic_request_exception(mock_validate_output, mock_validate_roadmap, mock_requests_post, caplog):
    """Test CLI handles other requests.exceptions.RequestException."""
    # Corrected: Set log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure the mock requests.post to raise a generic RequestException
    mock_requests_post.side_effect = requests.exceptions.Timeout("Mock timeout")

    with patch('sys.argv', ['main.py']), \
         pytest.raises(SystemExit) as excinfo:
        cli_entry_point()

    # Verify requests.post was called
    mock_requests_post.assert_called_once()
    # Verify error message is logged, including the exception details
    assert "Calling API to initiate workflow at http://127.0.0.1:5000/genesis/drive_workflow..." in caplog.text
    assert "An error occurred during API request to http://127.0.0.1:5000/genesis/drive_workflow: Mock timeout" in caplog.text
    # Verify script exited with code 1
    assert excinfo.value.code == 1

@patch('src.cli.main._validate_roadmap_path', return_value=os.path.abspath("ROADMAP.json"))
@patch('src.cli.main._validate_output_dir', return_value=os.path.abspath("./output"))
def test_cli_api_call_unexpected_exception(mock_validate_output, mock_validate_roadmap, mock_requests_post, caplog):
    """Test CLI handles unexpected generic Exception during API call process."""
    # Corrected: Set log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure the mock requests.post to raise a generic Exception
    mock_requests_post.side_effect = Exception("Unexpected error during request")

    with patch('sys.argv', ['main.py']), \
         pytest.raises(SystemExit) as excinfo:
        cli_entry_point()

    # Verify requests.post was called
    mock_requests_post.assert_called_once()
    # Verify error message is logged, including the exception details and traceback info
    assert "Calling API to initiate workflow at http://127.0.0.1:5000/genesis/drive_workflow..." in caplog.text
    assert "An unexpected error occurred: Unexpected error during request" in caplog.text
    assert "Traceback (most recent call last):" in caplog.text # Check for traceback info
    # Verify script exited with code 1
    assert excinfo.value.code == 1

# Removed the old tests that directly interacted with WorkflowDriver as that logic is now in the API.
# The tests above cover the CLI's new role of calling the API endpoint.