# tests/test_drive_workflow_endpoint.py
import pytest
import json
from unittest.mock import patch, MagicMock
import os # Import os for path testing
import logging # Add this import at the top

# Assuming the Flask app instance is named 'app' in src.api.server
# We need to import the app instance created in src.api.server
from src.api.server import app # Import the Flask app instance
from src.core.automation.workflow_driver import WorkflowDriver, Context # Import WorkflowDriver and Context for mocking

# Fixture for the Flask test client
@pytest.fixture
def client():
    # Ensure testing configuration if needed (e.g., app.config['TESTING'] = True)
    app.config['TESTING'] = True
    with app.test_client() as client:
        yield client

# Fixture to mock the WorkflowDriver
@pytest.fixture
def mock_workflow_driver():
    with patch('src.api.routes.workflow_endpoints.WorkflowDriver') as MockDriver:
        mock_instance = MockDriver.return_value
        # Mock the start_workflow method specifically
        mock_instance.start_workflow = MagicMock()
        yield mock_instance # Yield the mock instance

# Fixture to patch the _is_safe_path helper function
@pytest.fixture
def mock_is_safe_path():
    with patch('src.api.routes.workflow_endpoints._is_safe_path') as mock_helper:
        # By default, make it return True for valid paths
        mock_helper.return_value = True
        yield mock_helper # Yield the mock helper


def test_drive_workflow_valid_request(client, mock_workflow_driver, mock_is_safe_path):
    """Test POST /genesis/drive_workflow with valid request."""
    payload = {"roadmap_path": "ROADMAP.json", "output_dir": "output"}
    response = client.post('/genesis/drive_workflow', json=payload)

    assert response.status_code == 200
    assert json.loads(response.data) == {"status": "success", "message": "Workflow initiated"}
    # Verify WorkflowDriver.start_workflow was called with correct args
    mock_workflow_driver.start_workflow.assert_called_once()
    # Check the arguments passed to start_workflow
    # The first argument is self, then roadmap_path, output_dir, context
    # Need to be careful with mock arguments - it will be called on the mock instance
    called_args, called_kwargs = mock_workflow_driver.start_workflow.call_args
    assert len(called_args) == 3 # Should be roadmap_path, output_dir, context
    assert called_args[0] == "ROADMAP.json"
    assert called_args[1] == "output"
    # Check if the third argument is an instance of Context
    assert isinstance(called_args[2], Context)
    # Verify _is_safe_path was called for both paths and returned True (mocked)
    assert mock_is_safe_path.call_count == 2
    # Note: Checking the exact paths passed to _is_safe_path might be tricky due to os.getcwd()
    # We can check if it was called with the expected arguments structure
    mock_is_safe_path.assert_any_call(os.getcwd(), "ROADMAP.json")
    mock_is_safe_path.assert_any_call(os.getcwd(), "output")


def test_drive_workflow_missing_roadmap_path(client, mock_workflow_driver, mock_is_safe_path):
    """Test POST /genesis/drive_workflow with missing roadmap_path."""
    payload = {"output_dir": "output"}
    response = client.post('/genesis/drive_workflow', json=payload)

    assert response.status_code == 400
    response_data = json.loads(response.data)
    assert response_data["status"] == "error"
    assert "Missing or invalid 'roadmap_path'" in response_data["message"]
    mock_workflow_driver.start_workflow.assert_not_called()
    mock_is_safe_path.assert_not_called() # Should not get to path validation

def test_drive_workflow_missing_output_dir(client, mock_workflow_driver, mock_is_safe_path):
    """Test POST /genesis/drive_workflow with missing output_dir."""
    payload = {"roadmap_path": "ROADMAP.json"}
    response = client.post('/genesis/drive_workflow', json=payload)

    assert response.status_code == 400
    response_data = json.loads(response.data)
    assert response_data["status"] == "error"
    assert "Missing or invalid 'output_dir'" in response_data["message"]
    mock_workflow_driver.start_workflow.assert_not_called()
    mock_is_safe_path.assert_not_called() # Should not get to path validation

def test_drive_workflow_invalid_json(client, mock_workflow_driver, mock_is_safe_path):
    """Test POST /genesis/drive_workflow with invalid JSON."""
    # client.post expects 'json' or 'data', passing malformed string to 'data'
    response = client.post('/genesis/drive_workflow', data="not a json", content_type='application/json')

    assert response.status_code == 400 # Flask automatically handles malformed JSON with 400
    mock_workflow_driver.start_workflow.assert_not_called()
    mock_is_safe_path.assert_not_called() # Should not get this far


def test_drive_workflow_path_traversal_roadmap(client, mock_workflow_driver, mock_is_safe_path):
    """Test POST /genesis/drive_workflow with path traversal in roadmap_path."""
    # Make _is_safe_path return False for this specific test
    mock_is_safe_path.return_value = False
    payload = {"roadmap_path": "../sensitive_file", "output_dir": "output"}
    response = client.post('/genesis/drive_workflow', json=payload)

    assert response.status_code == 400
    response_data = json.loads(response.data)
    assert response_data["status"] == "error"
    assert "Invalid 'roadmap_path' format or content" in response_data["message"]
    mock_workflow_driver.start_workflow.assert_not_called()
    # _is_safe_path should have been called for roadmap_path
    mock_is_safe_path.assert_called_once_with(os.getcwd(), "../sensitive_file")


def test_drive_workflow_path_traversal_output_dir(client, mock_workflow_driver, mock_is_safe_path):
    """Test POST /genesis/drive_workflow with path traversal in output_dir."""
    # Configure _is_safe_path to return True for roadmap_path but False for output_dir
    mock_is_safe_path.side_effect = lambda base, path: path != "../malicious_output_dir"

    payload = {"roadmap_path": "ROADMAP.json", "output_dir": "../malicious_output_dir"}
    response = client.post('/genesis/drive_workflow', json=payload)

    assert response.status_code == 400
    response_data = json.loads(response.data)
    assert response_data["status"] == "error"
    assert "Invalid 'output_dir' format or content" in response_data["message"]
    mock_workflow_driver.start_workflow.assert_not_called()
    # _is_safe_path should be called for both, but the check for output_dir fails
    # It's called first for roadmap_path (returns True by side_effect), then for output_dir (returns False)
    assert mock_is_safe_path.call_count == 2
    mock_is_safe_path.assert_any_call(os.getcwd(), "ROADMAP.json")
    mock_is_safe_path.assert_called_with(os.getcwd(), "../malicious_output_dir")


def test_drive_workflow_driver_exception(client, mock_workflow_driver, mock_is_safe_path, caplog):
    """Test POST /genesis/drive_workflow when WorkflowDriver raises exception."""
    # Set _is_safe_path to always return True for this test
    mock_is_safe_path.return_value = True
    # Make WorkflowDriver.start_workflow raise an exception
    mock_workflow_driver.start_workflow.side_effect = Exception("Driver start failed")
    caplog.set_level(logging.ERROR) # Capture error log

    payload = {"roadmap_path": "ROADMAP.json", "output_dir": "output"}
    response = client.post('/genesis/drive_workflow', json=payload)

    assert response.status_code == 500
    response_data = json.loads(response.data)
    assert response_data["status"] == "error"
    assert "Internal server error during workflow initiation" in response_data["message"]
    # Check if the driver's start_workflow was still attempted
    mock_workflow_driver.start_workflow.assert_called_once()
    # Check the error was logged
    assert "Error initiating workflow: Driver start failed" in caplog.text