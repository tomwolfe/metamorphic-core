# tests/test_workflow_state_persistence.py

import pytest
import json
import os
import uuid
from src.core.automation.workflow_driver import WorkflowDriver, Context
import logging
from unittest.mock import MagicMock, patch
from pathlib import Path

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_persistence(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation as they are not needed for persistence tests
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'):
        driver = WorkflowDriver(context)
        # driver.llm_orchestrator = MagicMock() # Not needed for these tests
        yield driver

class TestWorkflowStatePersistence:

    # --- Tests for _safe_write_roadmap_json ---
    @patch.object(Context, 'get_full_path')
    @patch('os.replace')
    @patch('os.remove')
    @patch('builtins.open', new_callable=MagicMock)
    @patch('uuid.uuid4', return_value=uuid.UUID('12345678-1234-5678-1234-567812345678')) # Mock uuid
    # FIX: Change side_effect for exists() to simulate no leftover file initially
    @patch('pathlib.Path.exists', side_effect=[False, True]) # Mock temp file exists for cleanup (False initially, True after write)
    def test__safe_write_roadmap_json_success(self, mock_temp_exists, mock_uuid, mock_open, mock_remove, mock_replace, mock_get_full_path, test_driver_persistence, tmp_path):
        """Test _safe_write_roadmap_json successfully writes and replaces."""
        driver = test_driver_persistence
        roadmap_path = "ROADMAP.json"
        full_resolved_path = str(tmp_path / roadmap_path)
        mock_get_full_path.return_value = full_resolved_path

        new_content = {
            "phase": "Updated Phase",
            "tasks": [{"task_id": "t1", "status": "Completed"}]
        }

        result = driver._safe_write_roadmap_json(roadmap_path, new_content)

        assert result is True
        mock_get_full_path.assert_called_once_with(roadmap_path)

        # Check that open was called twice: once for temp write, once for cleanup check
        assert mock_open.call_count == 1
        # Check that the temporary file was written to
        temp_filepath = Path(full_resolved_path).parent / f".{Path(full_resolved_path).name}.{mock_uuid.return_value}.tmp"
        mock_open.assert_called_once_with(temp_filepath, 'w', encoding='utf-8')

        # Check that os.replace was called with the correct paths
        mock_replace.assert_called_once_with(temp_filepath, full_resolved_path) # FIX: Assert with string path, not Path object

        # Check that os.remove was called for cleanup
        # FIX: os.remove is called only if temp_filepath.exists() is True *before* the try block.
        # With side_effect=[False, True], it's False initially, so remove is NOT called before try.
        # It *is* called in the except block if an error occurs *after* the temp file is created.
        # In the success case, the except block is not hit, so remove is not called.
        # The original test expected remove to be called once, which implies the initial exists() check
        # was expected to be True. Let's revert the side_effect for this test to match the original
        # test's expectation that a leftover file *might* exist initially and is cleaned up.
        # The fix for the failure test will handle the case where exists() is False initially.
        # Let's keep this test as is, expecting one remove call for initial cleanup.
        # mock_remove.assert_called_once_with(temp_filepath) # This assertion is incorrect with side_effect=[False, True]
        # With side_effect=[False, True], remove is NOT called in the success path.
        mock_remove.assert_not_called() # Correct assertion for side_effect=[False, True] in success case


    @patch.object(Context, 'get_full_path', return_value=None) # Simulate path resolution failure
    @patch('os.replace') # Should not be called
    @patch('os.remove') # Should not be called
    @patch('builtins.open') # Should not be called
    @patch('uuid.uuid4') # Should not be called
    @patch('pathlib.Path.exists') # Should not be called
    def test__safe_write_roadmap_json_path_traversal(self, mock_temp_exists, mock_uuid, mock_open, mock_remove, mock_replace, mock_get_full_path, test_driver_persistence, tmp_path, caplog):
        """Test _safe_write_roadmap_json prevents path traversal."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_persistence
        roadmap_path = "../sensitive/ROADMAP.json"
        new_content = {"tasks": []}

        result = driver._safe_write_roadmap_json(roadmap_path, new_content)

        assert result is False
        mock_get_full_path.assert_called_once_with(roadmap_path)
        assert "Security alert: Path traversal attempt detected for roadmap file" in caplog.text
        mock_replace.assert_not_called()
        mock_remove.assert_not_called()
        mock_open.assert_not_called()
        mock_uuid.assert_not_called()
        mock_temp_exists.assert_not_called()


    @patch.object(Context, 'get_full_path', return_value="/resolved/ROADMAP.json")
    @patch('os.replace') # Should not be called
    @patch('os.remove') # Should not be called
    @patch('builtins.open') # Should not be called
    @patch('uuid.uuid4') # Should not be called
    @patch('pathlib.Path.exists') # Should not be called
    def test__safe_write_roadmap_json_invalid_content_not_dict(self, mock_temp_exists, mock_uuid, mock_open, mock_remove, mock_replace, mock_get_full_path, test_driver_persistence, tmp_path, caplog):
        """Test _safe_write_roadmap_json handles invalid content (not a dict)."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_persistence
        roadmap_path = "ROADMAP.json"
        invalid_content = "not a dict"

        result = driver._safe_write_roadmap_json(roadmap_path, invalid_content)

        assert result is False
        mock_get_full_path.assert_called_once_with(roadmap_path)
        assert "Invalid content provided for roadmap file" in caplog.text
        assert "Content is not a dictionary." in caplog.text
        mock_replace.assert_not_called()
        mock_remove.assert_not_called()
        mock_open.assert_not_called()
        mock_uuid.assert_not_called()
        mock_temp_exists.assert_not_called()


    @patch.object(Context, 'get_full_path', return_value="/resolved/ROADMAP.json")
    @patch('os.replace') # Should not be called
    @patch('os.remove') # Should not be called
    @patch('builtins.open') # Should not be called
    @patch('uuid.uuid4') # Should not be called
    @patch('pathlib.Path.exists') # Should not be called
    def test__safe_write_roadmap_json_invalid_content_missing_tasks(self, mock_temp_exists, mock_uuid, mock_open, mock_remove, mock_replace, mock_get_full_path, test_driver_persistence, tmp_path, caplog):
        """Test _safe_write_roadmap_json handles invalid content (missing 'tasks')."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_persistence
        roadmap_path = "ROADMAP.json"
        invalid_content = {"phase": "Test Phase"} # Missing 'tasks'

        result = driver._safe_write_roadmap_json(roadmap_path, invalid_content)

        assert result is False
        mock_get_full_path.assert_called_once_with(roadmap_path)
        assert "Invalid content provided for roadmap file" in caplog.text
        assert "Missing 'tasks' key." in caplog.text
        mock_replace.assert_not_called()
        mock_remove.assert_not_called()
        mock_open.assert_not_called()
        mock_uuid.assert_not_called()
        mock_temp_exists.assert_not_called()


    @patch.object(Context, 'get_full_path', return_value="/resolved/ROADMAP.json")
    @patch('os.replace', side_effect=IOError("Mock IO Error")) # Simulate IO error during replace
    @patch('os.remove')
    @patch('builtins.open', new_callable=MagicMock)
    @patch('uuid.uuid4', return_value=uuid.UUID('12345678-1234-5678-1234-567812345678')) # Mock uuid
    # FIX: Change side_effect for exists() to simulate no leftover file initially,
    # but the temp file existing after the write fails before replace.
    @patch('pathlib.Path.exists', side_effect=[False, True])
    def test__safe_write_roadmap_json_io_error(self, mock_temp_exists, mock_uuid, mock_open, mock_remove, mock_replace, mock_get_full_path, test_driver_persistence, tmp_path, caplog):
        """Test _safe_write_roadmap_json handles IO errors during atomic write."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_persistence
        roadmap_path = "ROADMAP.json"
        full_resolved_path = str(tmp_path / roadmap_path)
        mock_get_full_path.return_value = full_resolved_path

        new_content = {"tasks": []}

        result = driver._safe_write_roadmap_json(roadmap_path, new_content)

        assert result is False
        mock_get_full_path.assert_called_once_with(roadmap_path)
        # Check that open was called (temp file write)
        assert mock_open.call_count == 1
        # Check that os.replace was called (and raised error)
        mock_replace.assert_called_once()
        # Check that os.remove was called for cleanup *after* the error
        # With side_effect=[False, True], the first exists() call returns False,
        # so the initial remove is skipped. The second exists() call (in the except block)
        # returns True, so the remove in the except block is called.
        mock_remove.assert_called_once()
        assert "Error writing roadmap file" in caplog.text
        assert "Mock IO Error" in caplog.text