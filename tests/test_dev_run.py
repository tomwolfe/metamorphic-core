# tests/test_dev_run.py
import pytest
import subprocess
import sys
import argparse
import os
import logging
from unittest.mock import patch, MagicMock, call, ANY # Import ANY
# Import the function directly for easier testing
# Assuming dev_run.py is in the project root relative to the tests directory
# This import path might need adjustment based on actual project structure
# If running pytest from the project root, 'dev_run' should work.
# If running pytest from tests/, you might need '..dev_run' or similar depending on setup.
# For this response, assuming 'dev_run' is directly importable when running tests.
from dev_run import dev_run_workflow
import requests # Added import
import time     # Added import

# Configure logging for tests
# Use basicConfig only if no handlers are already configured
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture to capture SystemExit
@pytest.fixture(scope="function")
def exit_mock(mocker):
    # Patch sys.exit to raise SystemExit instead of exiting
    return mocker.patch('sys.exit', side_effect=SystemExit)

# Fixture to mock subprocess.run
@pytest.fixture(scope="function")
def mock_subprocess_run(mocker):
    return mocker.patch('subprocess.run')

# Fixture to mock requests.get for health checks
@pytest.fixture(scope="function")
def mock_requests_get(mocker):
    return mocker.patch('requests.get')


# Test Case 1: Successful Execution Flow
def test_dev_run_workflow_success(exit_mock, mock_subprocess_run, mock_requests_get, caplog, capsys):
    """
    Test Case 1: Successful Execution Flow
    Description: Mock subprocess.run to return success (returncode 0, empty stderr) for both the docker-compose and python calls.
    Mock requests.get to return a successful health check response.
    Predicted Outcome: Pass. The script should call subprocess.run twice with the correct commands and arguments, perform health checks, log success messages, and exit with code 0.
    Justification: Verifies the correct sequence of calls and successful path, including the new health check.
    """
    caplog.set_level(logging.INFO)
    # Configure mock_subprocess_run side_effect for two calls: docker success, cli success
    mock_subprocess_run.side_effect = [
        MagicMock(stdout="Docker restarted", stderr="", returncode=0), # docker-compose restart success
        MagicMock(stdout="CLI workflow initiated", stderr="", returncode=0) # python src/cli/main.py success
    ]
    # Configure mock_requests_get to return a successful health check response
    mock_requests_get.return_value = MagicMock(status_code=200, json=lambda: {"status": "ready"})


    # Patch sys.argv for default arguments
    with patch('sys.argv', ['dev_run.py']):
        # Call the function under test
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    # Assertions
    # Check sys.exit was called with code 0
    exit_mock.assert_called_once_with(0)
    # Removed: assert excinfo.value.code == 0

    # Check subprocess.run was called twice with correct commands
    assert mock_subprocess_run.call_count == 2
    mock_subprocess_run.assert_has_calls([
        call(
            ["docker-compose", "restart", "metamorphic-core"],
            capture_output=True,
            text=True,
            check=False
            # REMOVED env=ANY here
        ),
        call(
            [sys.executable, "src/cli/main.py", "--roadmap", "ROADMAP.json", "--output-dir", "./output"],
            cwd=os.getcwd(),
            capture_output=True,
            text=True,
            check=False,
            env=ANY # KEPT env=ANY here
        )
    ])

    # Check requests.get was called at least once for health check
    mock_requests_get.assert_called()
    mock_requests_get.assert_called_with("http://localhost:5000/genesis/health", timeout=2)


    # Check logs
    assert "Attempting to restart 'metamorphic-core' Docker service..." in caplog.text
    assert "Docker Compose Restart STDOUT:\nDocker restarted" in caplog.text
    assert "'metamorphic-core' service restarted successfully." in caplog.text
    assert "Attempting to contact API server at http://localhost:5000/genesis/health..." in caplog.text # New log
    assert "API server is healthy and ready." in caplog.text # New log
    assert "Initiating workflow via CLI with roadmap='ROADMAP.json' and output-dir='./output'..." in caplog.text
    assert "CLI Execution STDOUT:\nCLI workflow initiated" in caplog.text
    assert "Workflow initiated successfully via CLI." in caplog.text
    assert "Development workflow script finished." in caplog.text

    # Check stdout/stderr captured by capsys (should be empty as logs are used)
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""


# Test Case 2: Docker Restart Failure
def test_dev_run_workflow_docker_fail(exit_mock, mock_subprocess_run, mock_requests_get, caplog, capsys):
    """
    Test Case 2: Docker Restart Failure
    Description: Mock subprocess.run for the docker-compose call to return a non-zero exit code (e.g., 1) and some stderr.
    Predicted Outcome: Pass. The script should call subprocess.run for docker-compose, detect the non-zero return code, log an error including stderr, and exit with code 1. The health check and python src/cli/main.py call should not occur.
    Justification: Verifies error handling for the first command and correct early exit before health check.
    """
    # FIX: Change log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure mock_subprocess_run side_effect for docker failure
    mock_subprocess_run.side_effect = [
        MagicMock(stdout="Docker stdout", stderr="Docker failed", returncode=1), # docker-compose restart failure
        # The health check and second call (python cli) should not happen
    ]

    # Patch sys.argv for default arguments
    with patch('sys.argv', ['dev_run.py']):
        # Call the function under test
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    # Assertions
    # Check sys.exit was called with code 1
    exit_mock.assert_called_once_with(1)
    # Removed: assert excinfo.value.code == 1

    # Check subprocess.run was called only once (for docker)
    assert mock_subprocess_run.call_count == 1
    mock_subprocess_run.assert_called_once_with(
        ["docker-compose", "restart", "metamorphic-core"],
        capture_output=True,
        text=True,
        check=False
        # REMOVED env=ANY here
    )

    # Health check should NOT be called
    mock_requests_get.assert_not_called()

    # Check logs
    assert "Attempting to restart 'metamorphic-core' Docker service..." in caplog.text
    assert "Docker Compose Restart STDOUT:\nDocker stdout" in caplog.text # Corrected assertion
    assert "Docker Compose Restart STDERR:\nDocker failed" in caplog.text # Warning log for stderr
    assert "Docker Compose Restart failed with exit code 1." in caplog.text # Error log for failure
    assert "Please ensure Docker is running and 'metamorphic-core' service is defined in docker-compose.yml." in caplog.text
    assert "Attempting to contact API server" not in caplog.text # Ensure health check was skipped
    assert "Initiating workflow via CLI" not in caplog.text # Ensure cli call was skipped

    # Check stdout/stderr captured by capsys
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""

# Test Case 3: CLI Execution Failure
def test_dev_run_workflow_cli_fail(exit_mock, mock_subprocess_run, mock_requests_get, caplog, capsys):
    """
    Test Case 3: CLI Execution Failure
    Description: Mock subprocess.run for the docker-compose call to succeed (returncode 0),
    mock requests.get for health check to succeed, but the python src/cli/main.py call
    to return a non-zero exit code (e.g., 1) and some stderr.
    Predicted Outcome: Pass. The script should call subprocess.run for docker-compose,
    perform health checks, then call subprocess.run for python, detect the non-zero
    return code from the second call, log an error including stderr, and exit with code 1.
    Justification: Verifies error handling for the second command after successful health check.
    """
    # FIX: Change log level to INFO to capture the initial log message
    caplog.set_level(logging.INFO)
    # Configure mock_subprocess_run side_effect for docker success, cli failure
    mock_subprocess_run.side_effect = [
        MagicMock(stdout="Docker restarted", stderr="", returncode=0), # docker-compose restart success
        MagicMock(stdout="CLI stdout", stderr="CLI failed", returncode=1) # python src/cli/main.py failure
    ]
    # Configure mock_requests_get to return a successful health check response
    mock_requests_get.return_value = MagicMock(status_code=200, json=lambda: {"status": "ready"})


    # Patch sys.argv for default arguments
    with patch('sys.argv', ['dev_run.py']):
        # Call the function under test
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    # Assertions
    # Check sys.exit was called with code 1
    exit_mock.assert_called_once_with(1)
    # Removed: assert excinfo.value.code == 1

    # Check subprocess.run was called twice
    assert mock_subprocess_run.call_count == 2
    mock_subprocess_run.assert_has_calls([
        call(
            ["docker-compose", "restart", "metamorphic-core"],
            capture_output=True,
            text=True,
            check=False
            # REMOVED env=ANY here
        ),
        call(
            [sys.executable, "src/cli/main.py", "--roadmap", "ROADMAP.json", "--output-dir", "./output"],
            cwd=os.getcwd(),
            capture_output=True,
            text=True,
            check=False,
            env=ANY # KEPT env=ANY here
        )
    ])

    # Health check should be called at least once
    mock_requests_get.assert_called()


    # Check logs
    assert "Attempting to restart 'metamorphic-core' Docker service..." in caplog.text
    assert "'metamorphic-core' service restarted successfully." in caplog.text
    assert "API server is healthy and ready." in caplog.text # New log
    assert "Initiating workflow via CLI with roadmap='ROADMAP.json' and output-dir='./output'..." in caplog.text
    assert "CLI Execution STDOUT:\nCLI stdout" in caplog.text
    assert "CLI Execution STDERR:\nCLI failed" in caplog.text # Warning log for stderr
    assert "CLI execution failed with exit code 1." in caplog.text # Error log for failure
    assert "Workflow initiated successfully via CLI." not in caplog.text # Ensure success log was skipped

    # Check stdout/stderr captured by capsys
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""

# Test Case 4: Argument Passing
def test_dev_run_workflow_custom_args(exit_mock, mock_subprocess_run, mock_requests_get, caplog, capsys):
    """
    Test Case 4: Argument Passing
    Description: Run the script with custom arguments: python dev_run.py --roadmap custom/map.json --output-dir /tmp/output. Mock subprocess.run and assert that the arguments passed to the python src/cli/main.py call are [sys.executable, "src/cli/main.py", "--roadmap", "custom/map.json", "--output-dir", "/tmp/output"].
    Mock requests.get for health check to succeed.
    Predicted Outcome: Pass. The assertion on the mock subprocess.run call's arguments should succeed.
    Justification: Verifies that command-line arguments are correctly parsed and forwarded to the CLI script after a successful health check.
    """
    caplog.set_level(logging.INFO)
    # Configure mock_subprocess_run side_effect for two calls: docker success, cli success
    mock_subprocess_run.side_effect = [
        MagicMock(stdout="Docker restarted", stderr="", returncode=0), # docker-compose restart success
        MagicMock(stdout="CLI workflow initiated", stderr="", returncode=0) # python src/cli/main.py success
    ]
    # Configure mock_requests_get to return a successful health check response
    mock_requests_get.return_value = MagicMock(status_code=200, json=lambda: {"status": "ready"})


    custom_roadmap = "custom/map.json"
    custom_output = "/tmp/output"

    # Patch sys.argv for custom arguments
    with patch('sys.argv', ['dev_run.py', '--roadmap', custom_roadmap, '--output-dir', custom_output]):
        # Call the function under test
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    # Assertions
    # Check sys.exit was called with code 0
    exit_mock.assert_called_once_with(0)
    # Removed: assert excinfo.value.code == 0

    # Check subprocess.run was called twice
    assert mock_subprocess_run.call_count == 2
    mock_subprocess_run.assert_has_calls([
        call(
            ["docker-compose", "restart", "metamorphic-core"],
            capture_output=True,
            text=True,
            check=False
            # REMOVED env=ANY here
        ),
        call(
            [sys.executable, "src/cli/main.py", "--roadmap", custom_roadmap, "--output-dir", custom_output],
            cwd=os.getcwd(),
            capture_output=True,
            text=True,
            check=False,
            env=ANY # KEPT env=ANY here
        )
    ])

    # Health check should be called at least once
    mock_requests_get.assert_called()


    # Check logs reflect custom arguments
    assert f"Initiating workflow via CLI with roadmap='{custom_roadmap}' and output-dir='{custom_output}'..." in caplog.text

    # Check stdout/stderr captured by capsys
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""

# Test FileNotFoundError for docker-compose
def test_dev_run_workflow_docker_command_not_found(exit_mock, mock_subprocess_run, mock_requests_get, caplog):
    """Test handling of FileNotFoundError when 'docker-compose' is not found."""
    caplog.set_level(logging.ERROR)
    mock_subprocess_run.side_effect = FileNotFoundError("docker-compose not found")

    with patch('sys.argv', ['dev_run.py']):
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    exit_mock.assert_called_once_with(1)
    # Removed: assert excinfo.value.code == 1
    mock_subprocess_run.assert_called_once()
    assert "Error: 'docker-compose' command not found." in caplog.text
    assert "Please ensure Docker Compose is installed and in your system's PATH." in caplog.text
    # Health check should NOT be called
    mock_requests_get.assert_not_called()


# Test FileNotFoundError for src/cli/main.py
def test_dev_run_workflow_cli_script_not_found(exit_mock, mock_subprocess_run, mock_requests_get, caplog):
    """Test handling of FileNotFoundError when 'src/cli/main.py' is not found."""
    caplog.set_level(logging.ERROR)
    mock_subprocess_run.side_effect = [
        MagicMock(stdout="Docker restarted", stderr="", returncode=0), # docker-compose restart success
        FileNotFoundError("src/cli/main.py not found") # python src/cli/main.py not found
    ]
    # Configure mock_requests_get to return a successful health check response
    mock_requests_get.return_value = MagicMock(status_code=200, json=lambda: {"status": "ready"})


    with patch('sys.argv', ['dev_run.py']):
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    exit_mock.assert_called_once_with(1)
    # Removed: assert excinfo.value.code == 1
    assert mock_subprocess_run.call_count == 2 # Docker call happens, then CLI call fails
    assert "Error: 'src/cli/main.py' script not found." in caplog.text
    assert "Please ensure you are running this script from the project root directory." in caplog.text
    # Health check should be called at least once
    mock_requests_get.assert_called()


# Test generic exception during docker-compose run
def test_dev_run_workflow_docker_generic_exception(exit_mock, mock_subprocess_run, mock_requests_get, caplog):
    """Test handling of a generic exception during the docker-compose restart."""
    caplog.set_level(logging.ERROR)
    mock_subprocess_run.side_effect = Exception("Generic docker error")

    with patch('sys.argv', ['dev_run.py']):
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    exit_mock.assert_called_once_with(1)
    # Removed: assert excinfo.value.code == 1
    mock_subprocess_run.assert_called_once()
    assert "An unexpected error occurred during Docker Compose restart: Generic docker error" in caplog.text
    assert "Traceback (most recent call last):" in caplog.text # Check for traceback
    # Health check should NOT be called
    mock_requests_get.assert_not_called()


# Test generic exception during cli run
def test_dev_run_workflow_cli_generic_exception(exit_mock, mock_subprocess_run, mock_requests_get, caplog):
    """Test handling of a generic exception during the CLI execution."""
    caplog.set_level(logging.ERROR)
    mock_subprocess_run.side_effect = [
        MagicMock(stdout="Docker restarted", stderr="", returncode=0), # docker-compose restart success
        Exception("Generic cli error") # python src/cli/main.py generic exception
    ]
    # Configure mock_requests_get to return a successful health check response
    mock_requests_get.return_value = MagicMock(status_code=200, json=lambda: {"status": "ready"})


    with patch('sys.argv', ['dev_run.py']):
        with pytest.raises(SystemExit): # Removed 'as excinfo'
            dev_run_workflow()

    exit_mock.assert_called_once_with(1)
    # Removed: assert excinfo.value.code == 1
    assert mock_subprocess_run.call_count == 2
    assert "An unexpected error occurred during CLI execution: Generic cli error" in caplog.text
    # Health check should be called at least once
    mock_requests_get.assert_called()


# --- NEW TEST for Health Check Failure ---
def test_dev_run_workflow_health_check_fail(exit_mock, mock_subprocess_run, mock_requests_get, caplog):
    """Test handling when the API health check consistently fails."""
    caplog.set_level(logging.WARNING) # Capture warning logs from failed attempts
    caplog.set_level(logging.INFO) # Capture INFO logs as well for initial messages
    # Configure mock_subprocess_run for docker success
    mock_subprocess_run.return_value = MagicMock(stdout="Docker restarted", stderr="", returncode=0)
    # Configure mock_requests_get to consistently fail (e.g., raise an exception or return non-200)
    mock_requests_get.side_effect = requests.exceptions.ConnectionError("Health check failed")

    # Patch time.sleep to speed up the test
    with patch('time.sleep') as mock_sleep:
        mock_sleep.side_effect = lambda x: None # Make sleep a no-op

        with patch('sys.argv', ['dev_run.py']):
            with pytest.raises(SystemExit):
                dev_run_workflow()

    # Assertions
    exit_mock.assert_called_once_with(1)
    mock_subprocess_run.assert_called_once() # Docker restart should succeed
    # Health check should be attempted max_attempts times
    assert mock_requests_get.call_count == 30 # Default max_attempts is 30
    mock_requests_get.assert_called_with("http://localhost:5000/genesis/health", timeout=2)
    # CLI execution should NOT be called
    mock_subprocess_run.assert_has_calls([
        call(
            ["docker-compose", "restart", "metamorphic-core"],
            capture_output=True,
            text=True,
            check=False
            # REMOVED env=ANY here
        )
    ]) # Only the docker call should be in the history

    # Check logs
    assert "Attempting to restart 'metamorphic-core' Docker service..." in caplog.text
    assert "'metamorphic-core' service restarted successfully." in caplog.text
    assert "Attempting to contact API server at http://localhost:5000/genesis/health..." in caplog.text
    assert "API health check attempt 1/30 failed: Health check failed" in caplog.text
    assert "API server did not become healthy after multiple attempts. Exiting." in caplog.text