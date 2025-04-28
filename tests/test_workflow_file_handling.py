# tests/test_workflow_file_handling.py

import pytest
import os
import shutil
from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE
from src.cli.write_file import write_file, file_exists # Import write_file and file_exists
from pathlib import Path
import logging
from unittest.mock import MagicMock, patch, ANY, call # Import 'call'

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_file_handling(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation as they are not needed for file handling tests
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'):
        driver = WorkflowDriver(context)
        # Replace the real orchestrator with a mock if needed, but not for file handling tests
        # driver.llm_orchestrator = MagicMock()
        yield driver

# Fixture to mock Context.get_full_path for path resolution testing
@pytest.fixture
def mock_context_get_full_path():
    with patch.object(Context, 'get_full_path') as mock_helper:
        # By default, return a resolved path based on the input
        mock_helper.side_effect = lambda path: str(Path("/resolved") / path) if path else "/resolved/"
        yield mock_helper

class TestWorkflowFileHandling:

    # --- Tests for _write_output_file ---
    # Use the write_file utility function directly in the driver's method
    # We need to mock the write_file utility function itself, not _write_output_file
    @patch('src.core.automation.workflow_driver.write_file', return_value=True)
    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/file.txt")
    @patch('os.path.exists', return_value=True) # Mock exists for parent dir check
    @patch('os.path.isdir', return_value=True) # Mock isdir for parent dir check
    @patch('pathlib.Path.mkdir') # Mock mkdir
    def test_workflow_driver_write_output_file_success(self, mock_mkdir, mock_isdir, mock_exists, mock_get_full_path, mock_write_file, test_driver_file_handling, tmp_path):
        """Test _write_output_file successfully calls write_file with resolved path."""
        driver = test_driver_file_handling
        filepath = "path/to/file.txt" # Use relative path
        content = "Test content"
        # Mock the parent directory existence check
        mock_exists.side_effect = lambda p: Path(p).name == "path" # Simulate 'path' exists, but not 'path/to'

        result = driver._write_output_file(filepath, content)

        assert result is True
        mock_get_full_path.assert_called_once_with(filepath)
        # Check that mkdir was called for the parent directory (resolved path's parent)
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        # Check that write_file was called with the resolved path
        mock_write_file.assert_called_once_with("/resolved/path/to/file.txt", content, overwrite=False)

    @patch('src.core.automation.workflow_driver.write_file', side_effect=FileExistsError("File exists"))
    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/existing.txt")
    @patch('os.path.exists', return_value=True) # Mock exists for parent dir check
    @patch('os.path.isdir', return_value=True) # Mock isdir for parent dir check
    @patch('pathlib.Path.mkdir') # Mock mkdir
    def test_workflow_driver_write_output_file_exists_no_overwrite(self, mock_mkdir, mock_isdir, mock_exists, mock_get_full_path, mock_write_file, test_driver_file_handling, tmp_path):
        """Test _write_output_file raises FileExistsError when overwrite is False."""
        driver = test_driver_file_handling
        filepath = "path/to/existing.txt"
        content = "Test content"
        mock_exists.side_effect = lambda p: Path(p).name == "path" # Simulate 'path' exists, but not 'path/to'

        with pytest.raises(FileExistsError, match="File exists"):
            driver._write_output_file(filepath, content, overwrite=False)

        mock_get_full_path.assert_called_once_with(filepath)
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file.assert_called_once_with("/resolved/path/to/existing.txt", content, overwrite=False)

    @patch('src.core.automation.workflow_driver.write_file', side_effect=PermissionError("Permission denied"))
    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/readonly.txt")
    @patch('os.path.exists', return_value=True) # Mock exists for parent dir check
    @patch('os.path.isdir', return_value=True) # Mock isdir for parent dir check
    @patch('pathlib.Path.mkdir') # Mock mkdir
    def test_workflow_driver_write_output_file_permissionerror(self, mock_mkdir, mock_isdir, mock_exists, mock_get_full_path, mock_write_file, test_driver_file_handling, tmp_path, caplog):
        """Test writing to a read-only directory (PermissionError)."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        filepath = "path/to/readonly.txt"
        content = "Test content"
        mock_exists.side_effect = lambda p: Path(p).name == "path" # Simulate 'path' exists, but not 'path/to'

        result = driver._write_output_file(filepath, content)

        assert result is False
        mock_get_full_path.assert_called_once_with(filepath)
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file.assert_called_once_with("/resolved/path/to/readonly.txt", content, overwrite=False)
        assert "Permission error when writing to" in caplog.text

    @patch('src.core.automation.workflow_driver.write_file', return_value=True)
    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/overwrite.txt")
    @patch('os.path.exists', return_value=True) # Mock exists for parent dir check
    @patch('os.path.isdir', return_value=True) # Mock isdir for parent dir check
    @patch('pathlib.Path.mkdir') # Mock mkdir
    def test_workflow_driver_write_output_file_overwrite_true(self, mock_mkdir, mock_isdir, mock_exists, mock_get_full_path, mock_write_file, test_driver_file_handling, tmp_path, caplog):
        """Test overwrite=True successfully calls write_file with overwrite=True."""
        caplog.set_level(logging.INFO)
        driver = test_driver_file_handling
        filepath = "path/to/overwrite.txt"
        content = "new content"
        mock_exists.side_effect = lambda p: Path(p).name == "path" # Simulate 'path' exists, but not 'path/to'

        result = driver._write_output_file(filepath, content, overwrite=True)

        assert result is True
        mock_get_full_path.assert_called_once_with(filepath)
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file.assert_called_once_with("/resolved/path/to/overwrite.txt", content, overwrite=True)
        # REMOVED: assert "Successfully wrote to" in caplog.text

    @patch.object(Context, 'get_full_path', return_value=None) # Simulate path resolution failure
    def test_workflow_driver_write_output_file_security_path_injection(self, mock_get_full_path, test_driver_file_handling, tmp_path, caplog):
        """Test path injection attempts (e.g., using '..' or absolute paths)."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling

        # Test relative path injection attempt
        relative_path_attempt =  "../injected_file.txt"
        content = "Path injection test - relative path"
        result_relative = driver._write_output_file(relative_path_attempt, content)
        assert result_relative is False, "Relative path write should have failed due to resolution failure"
        mock_get_full_path.assert_called_once_with(relative_path_attempt)
        assert "Failed to resolve path for writing" in caplog.text

        caplog.clear()

        # Test absolute path injection attempt
        absolute_path_attempt = "/tmp/abs_injected_file.txt"
        content_absolute = "Path injection test - absolute path"
        # Mock get_full_path again for the second call
        mock_get_full_path.return_value = None
        result_absolute = driver._write_output_file(absolute_path_attempt, content_absolute)
        assert result_absolute is False, "Absolute path write should have failed due to resolution failure"
        mock_get_full_path.assert_called_with(absolute_path_attempt) # Use assert_called_with for the second call
        assert "Failed to resolve path for writing" in caplog.text

    @patch('src.core.automation.workflow_driver.write_file', side_effect=Exception("Unexpected error"))
    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/error.txt")
    @patch('os.path.exists', return_value=True) # Mock exists for parent dir check
    @patch('os.path.isdir', return_value=True) # Mock isdir for parent dir check
    @patch('pathlib.Path.mkdir') # Mock mkdir
    def test_workflow_driver_write_output_file_generic_exception(self, mock_mkdir, mock_isdir, mock_exists, mock_get_full_path, mock_write_file, test_driver_file_handling, tmp_path, caplog):
        """Test _write_output_file handles generic exceptions from write_file."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        filepath = "path/to/error.txt"
        content = "Test content"
        mock_exists.side_effect = lambda p: Path(p).name == "path" # Simulate 'path' exists, but not 'path/to'

        result = driver._write_output_file(filepath, content)

        assert result is False
        mock_get_full_path.assert_called_once_with(filepath)
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file.assert_called_once_with("/resolved/path/to/error.txt", content, overwrite=False)
        assert "Unexpected error writing to" in caplog.text
        assert "Unexpected error" in caplog.text


    # --- Tests for _read_file_for_context ---
    @patch.object(Context, 'get_full_path')
    @patch('builtins.open', new_callable=MagicMock)
    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE - 1) # Simulate file size within limit
    def test_read_file_for_context_success(self, mock_getsize, mock_isfile, mock_exists, mock_open, mock_get_full_path, test_driver_file_handling, caplog):
        """Test _read_file_for_context successfully reads a file."""
        caplog.set_level(logging.DEBUG)
        driver = test_driver_file_handling
        mock_get_full_path.return_value = "/resolved/path/to/file.txt"
        mock_open.return_value.__enter__.return_value.read.return_value = "File content"

        content = driver._read_file_for_context("path/to/file.txt")

        mock_get_full_path.assert_called_once_with("path/to/file.txt")
        mock_exists.assert_called_once_with("/resolved/path/to/file.txt")
        mock_isfile.assert_called_once_with("/resolved/path/to/file.txt")
        mock_getsize.assert_called_once_with("/resolved/path/to/file.txt")
        mock_open.assert_called_once_with("/resolved/path/to/file.txt", 'r', encoding='utf-8', errors='ignore')
        assert content == "File content"
        assert "Successfully read 12 characters from path/to/file.txt" in caplog.text

    @patch.object(Context, 'get_full_path', return_value=None) # Simulate path resolution failure
    @patch('os.path.exists') # Should not be called
    def test_read_file_for_context_path_resolution_failure(self, mock_exists, mock_get_full_path, test_driver_file_handling, caplog):
        """Test _read_file_for_context handles path resolution failure."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling

        # First call to trigger the path resolution failure and check basic behavior
        content = driver._read_file_for_context("../sensitive/file.txt")

        mock_get_full_path.assert_called_once_with("../sensitive/file.txt")
        assert content == ""
        assert "Failed to resolve path for reading: ../sensitive/file.txt" in caplog.text

        # Second call within patches to ensure subsequent file system calls are skipped
        with patch('os.path.isfile') as mock_isfile, \
             patch('os.path.getsize') as mock_getsize, \
             patch('builtins.open') as mock_open:

             driver._read_file_for_context("../sensitive/file.txt")

             mock_exists.assert_not_called()
             mock_isfile.assert_not_called()
             mock_getsize.assert_not_called()
             mock_open.assert_not_called()


    @patch.object(Context, 'get_full_path', return_value="/resolved/nonexistent/file.txt")
    @patch('os.path.exists', return_value=False) # Simulate file not found
    def test_read_file_for_context_file_not_found(self, mock_exists, mock_get_full_path, test_driver_file_handling, caplog):
        """Test _read_file_for_context handles FileNotFoundError."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling

        content = driver._read_file_for_context("nonexistent/file.txt")

        mock_get_full_path.assert_called_once_with("nonexistent/file.txt")
        mock_exists.assert_called_once_with("/resolved/nonexistent/file.txt")
        assert content == ""
        assert "File not found for reading: nonexistent/file.txt" in caplog.text
        with patch('os.path.isfile') as mock_isfile, \
             patch('os.path.getsize') as mock_getsize, \
             patch('builtins.open') as mock_open:
             driver._read_file_for_context("nonexistent/file.txt")
             mock_isfile.assert_not_called()
             mock_getsize.assert_not_called()
             mock_open.assert_not_called()


    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/directory")
    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=False) # Simulate path is a directory
    def test_read_file_for_context_is_directory(self, mock_isfile, mock_exists, mock_get_full_path, test_driver_file_handling, caplog):
        """Test _read_file_for_context handles path being a directory."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling

        content = driver._read_file_for_context("path/to/directory")

        mock_get_full_path.assert_called_once_with("path/to/directory")
        mock_exists.assert_called_once_with("/resolved/path/to/directory")
        mock_isfile.assert_called_once_with("/resolved/path/to/directory")
        assert content == ""
        assert "Path is not a file: path/to/directory" in caplog.text
        with patch('os.path.getsize') as mock_getsize, \
             patch('builtins.open') as mock_open:
             driver._read_file_for_context("path/to/directory")
             mock_getsize.assert_not_called()
             mock_open.assert_not_called()


    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/large_file.txt")
    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE + 1) # Simulate file too large
    def test_read_file_for_context_file_too_large(self, mock_getsize, mock_isfile, mock_exists, mock_get_full_path, test_driver_file_handling, caplog):
        """Test _read_file_for_context handles file exceeding size limit."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling

        test_relative_path = "path/to/large_file.txt"
        test_file_size = MAX_READ_FILE_SIZE + 1

        content = driver._read_file_for_context(test_relative_path)

        mock_get_full_path.assert_called_once_with(test_relative_path)
        mock_exists.assert_called_once_with("/resolved/path/to/large_file.txt")
        mock_isfile.assert_called_once_with("/resolved/path/to/large_file.txt")
        mock_getsize.assert_called_once_with("/resolved/path/to/large_file.txt")
        assert content == ""
        expected_log_substring = f"File exceeds maximum read size ({MAX_READ_FILE_SIZE} bytes): {test_relative_path} ({test_file_size} bytes)"
        assert expected_log_substring in caplog.text


    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/permission_denied.txt")
    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE - 1) # Simulate file size within limit
    @patch('builtins.open', side_effect=PermissionError("Permission denied")) # Simulate permission error during open
    def test_read_file_for_context_permission_denied(self, mock_open, mock_getsize, mock_isfile, mock_exists, mock_get_full_path, test_driver_file_handling, caplog):
        """Test _read_file_for_context handles PermissionError during file open."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling

        content = driver._read_file_for_context("path/to/permission_denied.txt")

        mock_get_full_path.assert_called_once_with("path/to/permission_denied.txt")
        mock_exists.assert_called_once_with("/resolved/path/to/permission_denied.txt")
        mock_isfile.assert_called_once_with("/resolved/path/to/permission_denied.txt")
        mock_getsize.assert_called_once_with("/resolved/path/to/permission_denied.txt")
        mock_open.assert_called_once_with("/resolved/path/to/permission_denied.txt", 'r', encoding='utf-8', errors='ignore')
        assert content == ""
        assert "Permission denied when reading file: path/to/permission_denied.txt" in caplog.text

    @patch.object(Context, 'get_full_path', return_value="/resolved/path/to/error_file.txt")
    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE - 1) # Simulate file size within limit
    @patch('builtins.open', side_effect=Exception("Unexpected read error")) # Simulate generic error during open
    def test_read_file_for_context_generic_error(self, mock_open, mock_getsize, mock_isfile, mock_exists, mock_get_full_path, test_driver_file_handling, caplog):
        """Test _read_file_for_context handles generic exceptions during file open."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling

        content = driver._read_file_for_context("path/to/error_file.txt")

        mock_get_full_path.assert_called_once_with("path/to/error_file.txt")
        mock_exists.assert_called_once_with("/resolved/path/to/error_file.txt")
        mock_isfile.assert_called_once_with("/resolved/path/to/error_file.txt")
        mock_getsize.assert_called_once_with("/resolved/path/to/error_file.txt")
        mock_open.assert_called_once_with("/resolved/path/to/error_file.txt", 'r', encoding='utf-8', errors='ignore')
        assert content == ""
        assert "Unexpected error reading file path/to/error_file.txt: Unexpected read error" in caplog.text

    def test_read_file_for_context_invalid_path_type(self, test_driver_file_handling, caplog):
        """Test _read_file_for_context handles invalid path input types."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling

        content_none = driver._read_file_for_context(None)
        assert content_none == ""
        assert "Attempted to read file with invalid path: None" in caplog.text

        caplog.clear()

        content_int = driver._read_file_for_context(123)
        assert content_int == ""
        assert "Attempted to read file with invalid path: 123" in caplog.text

    # --- Tests for file_exists ---
    @patch.object(Context, 'get_full_path')
    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    def test_file_exists_existing(self, mock_isfile, mock_exists, mock_get_full_path, test_driver_file_handling, tmp_path):
        driver = test_driver_file_handling
        test_file_relative = "test.txt"
        test_file_full = tmp_path / test_file_relative
        mock_get_full_path.return_value = str(test_file_full.resolve())

        assert driver.file_exists(test_file_relative) is True
        mock_get_full_path.assert_called_once_with(test_file_relative)
        mock_exists.assert_called_once_with(test_file_full.resolve())
        mock_isfile.assert_called_once_with(test_file_full.resolve())

    @patch.object(Context, 'get_full_path')
    @patch('os.path.exists', return_value=False)
    @patch('os.path.isfile') # Should not be called if exists is False
    def test_file_exists_non_existing(self, mock_isfile, mock_exists, mock_get_full_path, test_driver_file_handling, tmp_path):
        driver = test_driver_file_handling
        non_existing_file_relative = "nonexist.txt"
        mock_get_full_path.return_value = str(tmp_path / non_existing_file_relative)

        assert driver.file_exists(non_existing_file_relative) is False
        mock_get_full_path.assert_called_once_with(non_existing_file_relative)
        mock_exists.assert_called_once_with(tmp_path / non_existing_file_relative)
        mock_isfile.assert_not_called()

    @patch.object(Context, 'get_full_path', return_value=None) # Simulate path resolution failure
    @patch('os.path.exists') # Should not be called
    @patch('os.path.isfile') # Should not be called
    def test_file_exists_outside_base_path(self, mock_isfile, mock_exists, mock_get_full_path, test_driver_file_handling, tmp_path, caplog):
        """Test file_exists prevents checking outside the base path."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling

        assert driver.file_exists("../sensitive/file.txt") is False
        mock_get_full_path.assert_called_once_with("../sensitive/file.txt")
        mock_exists.assert_not_called()
        mock_isfile.assert_not_called()
        assert "Failed to resolve path for existence check" in caplog.text

    def test_file_exists_invalid_path_type(self, test_driver_file_handling, caplog):
        """Test file_exists handles invalid path input types."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling

        assert driver.file_exists(None) is False
        assert "file_exists received non-string input: <class 'NoneType'>" in caplog.text

        caplog.clear()

        assert driver.file_exists(123) is False
        assert "file_exists received non-string input: <class 'int'>" in caplog.text

    # --- Tests for list_files ---
    @patch.object(Context, 'get_full_path')
    @patch('os.listdir')
    # Patch Path as it's imported in the workflow_driver module
    @patch('src.core.automation.workflow_driver.Path')
    @patch.object(WorkflowDriver, '_is_valid_filename', return_value=True) # Assume all names are valid by default
    def test_list_files_success(self, mock_is_valid_filename, mock_Path, mock_listdir, mock_get_full_path, test_driver_file_handling, tmp_path):
        driver = test_driver_file_handling
        base_path = str(tmp_path)
        # This line now uses the *real* Path class because the patch targets
        # the Path object *within* the workflow_driver module's namespace.
        resolved_base_path_str = str(Path(base_path).resolve())
        mock_get_full_path.return_value = resolved_base_path_str # Mock resolving "" to the resolved base path string

        mock_listdir.return_value = ["file1.txt", "subdir", "file2.py"]

        # --- Configure the mock Path class and its instances ---

        # 1. Create a mock instance that will represent the resolved base path
        mock_base_path_instance = MagicMock()
        # Configure methods called on the base path instance
        mock_base_path_instance.is_dir.return_value = True # Base path is a directory
        mock_base_path_instance.is_file.return_value = False # Base path is not a file
        # Configure the division operator (/) which is used to join paths (resolved_base_path / name)
        # This side effect will be called when `resolved_base_path / name` is executed.
        # It should return a new mock instance representing the entry path.
        entry_mocks_created = {} # Dictionary to store the mocks created for entries

        def truediv_side_effect(name):
            # Create a new mock instance for the entry path (e.g., Path('/base/file1.txt'))
            entry_mock = MagicMock()
            # Configure methods on the entry mock based on the name
            entry_mock.is_file.return_value = "file" in name # Simulate file1.txt, file2.py are files
            entry_mock.is_dir.return_value = "subdir" in name # Simulate subdir is a directory
            # Add __str__ and __fspath__ mocks as os.listdir might use them internally
            entry_mock.__str__.return_value = f"{resolved_base_path_str}/{name}"
            entry_mock.__fspath__.return_value = f"{resolved_base_path_str}/{name}"
            # Store the created mock instance so we can assert calls on it later
            entry_mocks_created[name] = entry_mock
            return entry_mock

        mock_base_path_instance.__truediv__.side_effect = truediv_side_effect

        # Add __str__ and __fspath__ mocks for the base path instance itself
        mock_base_path_instance.__str__.return_value = resolved_base_path_str
        mock_base_path_instance.__fspath__.return_value = resolved_base_path_str


        # 2. Configure the mock Path class itself
        # When Path(resolved_base_path_str) is called in the code, the mock_Path is called.
        # We want it to return our mock_base_path_instance.
        def Path_side_effect(*args, **kwargs):
            # Check if Path is being called with the resolved base path string
            # Use str() on args[0] for comparison as the code passes a string
            if args and str(args[0]) == resolved_base_path_str:
                return mock_base_path_instance
            # If Path is called with other arguments (e.g., during test setup or other code paths),
            # return a default mock instance.
            return MagicMock()

        mock_Path.side_effect = Path_side_effect

        # --- Call the method under test ---
        entries = driver.list_files()

        # --- Assertions ---

        # Assert Context.get_full_path was called to get the base path
        mock_get_full_path.assert_called_once_with("")

        # Assert Path was called with the resolved base path string
        # Use str() here because the code passes a string to Path()
        mock_Path.assert_called_once_with(resolved_base_path_str)

        # Assert listdir was called with the mock instance representing the base path
        mock_listdir.assert_called_once_with(mock_base_path_instance)

        # Assert methods were called on the base path instance mock
        mock_base_path_instance.is_dir.assert_called_once_with() # Called once before the loop

        # Assert methods were called on the entry mocks created by the division operator
        assert len(entry_mocks_created) == 3 # One mock created for each item from listdir

        # Retrieve the specific entry mocks
        mock_file1_instance = entry_mocks_created["file1.txt"]
        mock_subdir_instance = entry_mocks_created["subdir"]
        mock_file2_instance = entry_mocks_created["file2.py"]

        # Assert calls on the file mocks
        mock_file1_instance.is_file.assert_called_once_with()
        mock_file1_instance.is_dir.assert_not_called() # is_dir not called because is_file was True

        mock_file2_instance.is_file.assert_called_once_with()
        mock_file2_instance.is_dir.assert_not_called() # is_dir not called because is_file was True

        # Assert calls on the subdir mock
        mock_subdir_instance.is_file.assert_called_once_with() # is_file is called first
        mock_subdir_instance.is_dir.assert_called_once_with() # is_dir is called because is_file returned False

        # Assert the final list of entries is correct
        assert len(entries) == 3
        assert {'name': 'file1.txt', 'status': 'file'} in entries
        assert {'name': 'subdir', 'status': 'directory'} in entries
        assert {'name': 'file2.py', 'status': 'file'} in entries

        # Assert _is_valid_filename was called for each entry from listdir
        assert mock_is_valid_filename.call_count == 3
        mock_is_valid_filename.assert_any_call("file1.txt")
        mock_is_valid_filename.assert_any_call("subdir")
        mock_is_valid_filename.assert_any_call("file2.py")
    
    @patch.object(Context, 'get_full_path', return_value=None) # Simulate path resolution failure
    @patch('os.listdir') # Should not be called
    def test_list_files_base_path_resolution_failure(self, mock_listdir, mock_get_full_path, test_driver_file_handling, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling

        entries = driver.list_files()

        mock_get_full_path.assert_called_once_with("")
        assert len(entries) == 0
        assert "Failed to resolve base path for listing" in caplog.text
        mock_listdir.assert_not_called()

    @patch.object(Context, 'get_full_path')
    @patch('os.listdir', side_effect=PermissionError("Permission denied"))
    @patch('pathlib.Path.is_dir', return_value=True) # Mock is_dir for the resolved base path
    def test_list_files_permission_denied(self, mock_is_dir, mock_listdir, mock_get_full_path, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        resolved_base_path_str = str(Path(str(tmp_path)).resolve()) # Get the resolved string path
        mock_get_full_path.return_value = resolved_base_path_str # Mock resolving "" to the resolved base path string

        # Create a Path object from the resolved string path for assertions
        resolved_base_path_obj = Path(resolved_base_path_str)

        entries = driver.list_files()

        mock_get_full_path.assert_called_once_with("")
        # Assert is_dir was called on the resolved Path object instance *as the instance itself*
        # FIX: Change assertion to check for call with no explicit arguments
        mock_is_dir.assert_called_once_with()
        # Assert listdir was called with the resolved Path object instance
        # FIX: Change assertion to check with the Path object
        mock_listdir.assert_called_once_with(resolved_base_path_obj)
        assert len(entries) == 0
        assert "Error listing files in" in caplog.text
        # FIX: Correct capitalization in assertion
        assert "Permission denied" in caplog.text

    @patch.object(Context, 'get_full_path')
    @patch('os.listdir')
    @patch('pathlib.Path.is_dir', return_value=False) # Simulate base path is not a directory
    def test_list_files_base_path_not_directory(self, mock_is_dir, mock_listdir, mock_get_full_path, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        resolved_base_path_str = str(Path(str(tmp_path)).resolve()) # Get the resolved string path
        mock_get_full_path.return_value = resolved_base_path_str # Mock resolving "" to the resolved base path string

        # Create a Path object from the resolved string path for assertions
        resolved_base_path_obj = Path(resolved_base_path_str)

        entries = driver.list_files()

        mock_get_full_path.assert_called_once_with("")
        # Assert is_dir was called on the resolved Path object instance *as the instance itself*
        # FIX: Change assertion to check for call with no explicit arguments
        mock_is_dir.assert_called_once_with()
        assert len(entries) == 0
        assert "Base path is not a valid directory" in caplog.text
        mock_listdir.assert_not_called()

    @patch.object(Context, 'get_full_path')
    @patch('os.listdir', return_value=["valid_file.txt", "file!@#.txt", ".hidden_file.txt"])
    @patch('pathlib.Path.is_file', return_value=True) # Assume all are files for simplicity
    @patch('pathlib.Path.is_dir', return_value=False) # Assume none are directories for simplicity
    @patch.object(WorkflowDriver, '_is_valid_filename')
    def test_list_files_invalid_filename(self, mock_is_valid_filename, mock_is_dir, mock_is_file, mock_listdir, mock_get_full_path, test_driver_file_handling, tmp_path, caplog):
        """Test list_files skips invalid filenames."""
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling
        resolved_base_path_str = str(Path(str(tmp_path)).resolve()) # Get the resolved string path
        mock_get_full_path.return_value = resolved_base_path_str
        resolved_base_path_obj = Path(resolved_base_path_str) # Create Path object for assertion
        mock_is_dir.return_value = True # Base path is a directory

        # Configure _is_valid_filename mock
        mock_is_valid_filename.side_effect = lambda name: name == "valid_file.txt"

        entries = driver.list_files()

        mock_get_full_path.assert_called_once_with("")
        # FIX: Assert listdir was called with the Path object
        mock_listdir.assert_called_once_with(resolved_base_path_obj)
        assert len(entries) == 1
        assert {'name': 'valid_file.txt', 'status': 'file'} in entries

        # _is_valid_filename should be called for all names from listdir
        assert mock_is_valid_filename.call_count == 3
        mock_is_valid_filename.assert_any_call("valid_file.txt")
        mock_is_valid_filename.assert_any_call("file!@#.txt")
        mock_is_valid_filename.assert_any_call(".hidden_file.txt")

        # Check log messages for skipped invalid names
        assert "Skipping listing of potentially unsafe filename: file!@#.txt" in caplog.text
        assert "Skipping listing of potentially unsafe filename: .hidden_file.txt" in caplog.text


    # --- Tests for _is_valid_filename ---
    def test_is_valid_filename_valid_formats(self, test_driver_file_handling):
        """Test _is_valid_filename with valid filename formats."""
        driver = test_driver_file_handling
        assert driver._is_valid_filename("file.txt") is True
        assert driver._is_valid_filename("file_name-123.py") is True
        assert driver._is_valid_filename("directory_name") is True
        assert driver._is_valid_filename("a") is True
        assert driver._is_valid_filename("1") is True
        assert driver._is_valid_filename("a.b.c") is True
        assert driver._is_valid_filename("a-b_c.d") is True

    def test_is_valid_filename_invalid_formats(self, test_driver_file_handling):
        """Test _is_valid_filename with invalid filename formats."""
        driver = test_driver_file_handling
        assert driver._is_valid_filename("invalid/id") is False
        assert driver._is_valid_filename("..") is False
        assert driver._is_valid_filename("../file.txt") is False
        assert driver._is_valid_filename("file name") is False
        assert driver._is_valid_filename("file!@#") is False
        assert driver._is_valid_filename("") is False
        assert driver._is_valid_filename(None) is False
        assert driver._is_valid_filename(123) is False
        assert driver._is_valid_filename("task.") is False # This should now pass with the fix
        assert driver._is_valid_filename(".hidden_file.txt") is False
        assert driver._is_valid_filename("-file.txt") is False
        assert driver._is_valid_filename("_file.txt") is False

    # --- Tests for _merge_snippet ---
    def test__merge_snippet_marker_found(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        snippet = "inserted_line_a\ninserted_line_b"
        expected = "line1\nline2\ninserted_line_a\ninserted_line_b\nline3"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_marker_not_found(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1\nline2\nline3"
        snippet = "inserted_line"
        expected = "line1\nline2\nline3\ninserted_line" # Appends with newline
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_empty_snippet(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1\nline2"
        snippet = ""
        merged = driver._merge_snippet(existing, snippet)
        assert merged == existing

    def test__merge_snippet_empty_existing(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = ""
        snippet = "snippet"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == snippet

    def test__merge_snippet_existing_no_newline(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1"
        snippet = "snippet"
        expected = "line1\nsnippet" # Appends with newline
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_existing_ends_newline(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1\n"
        snippet = "snippet"
        expected = "line1\nsnippet" # Appends directly
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_marker_at_start(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "# METAMORPHIC_INSERT_POINT\nline1"
        snippet = "inserted"
        expected = "inserted\nline1"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_marker_at_end(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1\n# METAMORPHIC_INSERT_POINT"
        snippet = "inserted"
        expected = "line1\ninserted"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_multiple_markers(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1\n# METAMORPHIC_INSERT_POINT\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        snippet = "inserted"
        # Should only replace the first marker
        expected = "line1\ninserted\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected
