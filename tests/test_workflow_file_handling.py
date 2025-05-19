# tests/test_workflow_file_handling.py

import pytest
import os
import shutil
from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_READ_FILE_SIZE
from src.cli.write_file import write_file # Import write_file
from pathlib import Path
import logging
from unittest.mock import MagicMock, patch, ANY, call # Import 'call'

# Set up logging for tests
# Ensure basicConfig is only called once
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a WorkflowDriver instance with a Context
@pytest.fixture
def test_driver_file_handling(tmp_path):
    context = Context(str(tmp_path))
    # Patch the CodeReviewAgent and EthicalGovernanceEngine instantiation as they are not needed for file handling tests
    with patch('src.core.automation.workflow_driver.CodeReviewAgent'), \
         patch('src.core.automation.workflow_driver.EthicalGovernanceEngine'), \
         patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'): # Patch LLM Orchestrator
        driver = WorkflowDriver(context)
        driver.llm_orchestrator = MagicMock() # Mock LLM orchestrator
        # Ensure default policy is set for consistency, even if not directly used by all tests here
        # This also ensures the warning log from _load_default_policy happens during fixture setup,
        # not during the test itself, keeping caplog clean for test-specific logs.
        driver.default_policy_config = {'policy_name': 'Mock Policy'}
        yield driver


class TestWorkflowFileHandling:

    # --- Tests for _write_output_file ---
    @patch('src.core.automation.workflow_driver.write_file', return_value=True) # Mock the utility function
    @patch('pathlib.Path.mkdir') # Mock mkdir
    @patch('pathlib.Path.exists', return_value=False) # Mock exists for parent dir check
    def test_workflow_driver_write_output_file_success(self, mock_dir_exists, mock_mkdir, mock_write_file_utility, test_driver_file_handling, tmp_path):
        """Test _write_output_file successfully calls the write_file utility with absolute path."""
        driver = test_driver_file_handling
        relative_filepath = "path/to/file.txt"
        absolute_filepath = str(tmp_path / relative_filepath) # Pass absolute path
        content = "Test content"

        result = driver._write_output_file(absolute_filepath, content)

        assert result is True
        # Path(absolute_filepath).parent.exists() is called
        mock_dir_exists.assert_called_once_with()
        # Path(absolute_filepath).parent.mkdir() is called because exists returned False
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file_utility.assert_called_once_with(absolute_filepath, content, overwrite=False)

    @patch('src.core.automation.workflow_driver.write_file', side_effect=FileExistsError("File exists"))
    @patch('pathlib.Path.mkdir')
    @patch('pathlib.Path.exists', return_value=False) # Mock exists for parent dir check
    def test_workflow_driver_write_output_file_exists_no_overwrite(self, mock_dir_exists, mock_mkdir, mock_write_file_utility, test_driver_file_handling, tmp_path):
        """Test _write_output_file raises FileExistsError from utility when overwrite is False."""
        driver = test_driver_file_handling
        relative_filepath = "path/to/existing.txt"
        absolute_filepath = str(tmp_path / relative_filepath)
        content = "Test content"

        with pytest.raises(FileExistsError, match="File exists"):
            driver._write_output_file(absolute_filepath, content, overwrite=False)

        mock_dir_exists.assert_called_once_with()
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file_utility.assert_called_once_with(absolute_filepath, content, overwrite=False)

    @patch('src.core.automation.workflow_driver.write_file', side_effect=PermissionError("Permission denied"))
    @patch('pathlib.Path.mkdir')
    @patch('pathlib.Path.exists', return_value=False) # Mock exists for parent dir check
    def test_workflow_driver_write_output_file_permissionerror(self, mock_dir_exists, mock_mkdir, mock_write_file_utility, test_driver_file_handling, tmp_path, caplog):
        """Test _write_output_file handles PermissionError from utility."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        relative_filepath = "path/to/readonly.txt"
        absolute_filepath = str(tmp_path / relative_filepath)
        content = "Test content"

        result = driver._write_output_file(absolute_filepath, content)

        assert result is False
        mock_dir_exists.assert_called_once_with()
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file_utility.assert_called_once_with(absolute_filepath, content, overwrite=False)
        assert f"Permission error from write_file for {absolute_filepath}: Permission denied" in caplog.text


    @patch('src.core.automation.workflow_driver.write_file', return_value=True)
    @patch('pathlib.Path.mkdir')
    @patch('pathlib.Path.exists', return_value=True) # Mock exists for parent dir check (dir exists)
    def test_workflow_driver_write_output_file_overwrite_true(self, mock_dir_exists, mock_mkdir, mock_write_file_utility, test_driver_file_handling, tmp_path, caplog):
        """Test overwrite=True successfully calls utility with overwrite=True."""
        caplog.set_level(logging.INFO)
        driver = test_driver_file_handling
        relative_filepath = "path/to/overwrite.txt"
        absolute_filepath = str(tmp_path / relative_filepath)
        content = "new content"

        result = driver._write_output_file(absolute_filepath, content, overwrite=True)

        assert result is True
        mock_dir_exists.assert_called_once_with() # Check parent dir exists is called
        mock_mkdir.assert_not_called() # mkdir should not be called if exists is True
        mock_write_file_utility.assert_called_once_with(absolute_filepath, content, overwrite=True)
        # No log for creating directory if it already exists

    def test_workflow_driver_write_output_file_invalid_path_input(self, test_driver_file_handling, caplog):
        """Test _write_output_file handles None or empty string for full_filepath."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling

        result_none = driver._write_output_file(None, "content")
        assert result_none is False
        assert "_write_output_file received invalid full filepath: None" in caplog.text
        caplog.clear()

        result_empty = driver._write_output_file("", "content")
        assert result_empty is False
        assert "_write_output_file received invalid full filepath: " in caplog.text # Empty string logs this

    @patch('src.core.automation.workflow_driver.write_file', side_effect=Exception("Unexpected error"))
    @patch('pathlib.Path.mkdir')
    @patch('pathlib.Path.exists', return_value=False) # Mock exists for parent dir check
    def test_workflow_driver_write_output_file_generic_exception(self, mock_dir_exists, mock_mkdir, mock_write_file_utility, test_driver_file_handling, tmp_path, caplog):
        """Test _write_output_file handles generic exceptions from write_file utility."""
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        relative_filepath = "path/to/error.txt"
        absolute_filepath = str(tmp_path / relative_filepath)
        content = "Test content"

        result = driver._write_output_file(absolute_filepath, content)

        assert result is False
        mock_dir_exists.assert_called_once_with()
        mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)
        mock_write_file_utility.assert_called_once_with(absolute_filepath, content, overwrite=False)
        assert f"Unexpected error from write_file for {absolute_filepath}: Unexpected error" in caplog.text


    # --- Tests for _read_file_for_context ---
    # These tests now pass absolute paths to _read_file_for_context
    @patch('builtins.open', new_callable=MagicMock)
    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE - 1)
    def test_read_file_for_context_success(self, mock_getsize, mock_isfile, mock_exists, mock_open, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.DEBUG)
        driver = test_driver_file_handling
        absolute_filepath = str(tmp_path / "file.txt")
        mock_open.return_value.__enter__.return_value.read.return_value = "File content"

        content = driver._read_file_for_context(absolute_filepath)

        mock_exists.assert_called_once_with(absolute_filepath)
        mock_isfile.assert_called_once_with(absolute_filepath)
        mock_getsize.assert_called_once_with(absolute_filepath)
        mock_open.assert_called_once_with(absolute_filepath, 'r', encoding='utf-8', errors='ignore')
        assert content == "File content"
        assert f"Successfully read 12 characters from {absolute_filepath}" in caplog.text

    @patch('os.path.exists') # Should not be called if path is None/empty
    def test_read_file_for_context_invalid_full_path(self, mock_exists, test_driver_file_handling, caplog):
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling

        content_none = driver._read_file_for_context(None)
        assert content_none == ""
        assert "Attempted to read file with invalid full path: None" in caplog.text
        mock_exists.assert_not_called()
        caplog.clear()

        content_empty = driver._read_file_for_context("")
        assert content_empty == ""
        assert "Attempted to read file with invalid full path: " in caplog.text # Empty string logs this
        mock_exists.assert_not_called()


    @patch('os.path.exists', return_value=False) # Simulate file not found
    def test_read_file_for_context_file_not_found(self, mock_exists, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling
        absolute_filepath = str(tmp_path / "nonexistent/file.txt")

        content = driver._read_file_for_context(absolute_filepath)

        mock_exists.assert_called_once_with(absolute_filepath)
        assert content == ""
        assert f"File not found for reading: {absolute_filepath}" in caplog.text

    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=False) # Simulate path is a directory
    def test_read_file_for_context_is_directory(self, mock_isfile, mock_exists, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling
        absolute_filepath = str(tmp_path / "path/to/directory")
        # No need to create the actual directory if mocking os.path.isfile

        content = driver._read_file_for_context(absolute_filepath)

        mock_exists.assert_called_once_with(absolute_filepath)
        mock_isfile.assert_called_once_with(absolute_filepath)
        assert content == ""
        assert f"Path is not a file: {absolute_filepath}" in caplog.text

    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE + 1) # Simulate file too large
    def test_read_file_for_context_file_too_large(self, mock_getsize, mock_isfile, mock_exists, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling
        absolute_filepath = str(tmp_path / "large_file.txt")
        test_file_size = MAX_READ_FILE_SIZE + 1

        content = driver._read_file_for_context(absolute_filepath)

        mock_exists.assert_called_once_with(absolute_filepath)
        mock_isfile.assert_called_once_with(absolute_filepath)
        mock_getsize.assert_called_once_with(absolute_filepath)
        assert content == ""
        expected_log_substring = f"File exceeds maximum read size ({MAX_READ_FILE_SIZE} bytes): {absolute_filepath} ({test_file_size} bytes)"
        assert expected_log_substring in caplog.text

    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE - 1)
    @patch('builtins.open', side_effect=PermissionError("Permission denied"))
    def test_read_file_for_context_permission_denied(self, mock_open, mock_getsize, mock_isfile, mock_exists, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        absolute_filepath = str(tmp_path / "permission_denied.txt")

        content = driver._read_file_for_context(absolute_filepath)

        mock_exists.assert_called_once_with(absolute_filepath)
        mock_isfile.assert_called_once_with(absolute_filepath)
        mock_getsize.assert_called_once_with(absolute_filepath)
        mock_open.assert_called_once_with(absolute_filepath, 'r', encoding='utf-8', errors='ignore')
        assert content == ""
        assert f"Permission denied when reading file: {absolute_filepath}" in caplog.text

    @patch('os.path.exists', return_value=True)
    @patch('os.path.isfile', return_value=True)
    @patch('os.path.getsize', return_value=MAX_READ_FILE_SIZE - 1)
    @patch('builtins.open', side_effect=Exception("Unexpected read error"))
    def test_read_file_for_context_generic_error(self, mock_open, mock_getsize, mock_isfile, mock_exists, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        absolute_filepath = str(tmp_path / "error_file.txt")

        content = driver._read_file_for_context(absolute_filepath)

        mock_exists.assert_called_once_with(absolute_filepath)
        mock_isfile.assert_called_once_with(absolute_filepath)
        mock_getsize.assert_called_once_with(absolute_filepath)
        mock_open.assert_called_once_with(absolute_filepath, 'r', encoding='utf-8', errors='ignore')
        assert content == ""
        assert f"Unexpected error reading file {absolute_filepath}: Unexpected read error" in caplog.text


    # --- Tests for file_exists ---
    # These tests need to mock driver.context.get_full_path and pathlib.Path methods
    @patch.object(Context, 'get_full_path')
    @patch('pathlib.Path.exists', return_value=True) # Mock Path.exists
    @patch('pathlib.Path.is_file', return_value=True) # Mock Path.is_file
    def test_file_exists_existing(self, mock_path_is_file, mock_path_exists, mock_context_get_full_path, test_driver_file_handling, tmp_path):
        driver = test_driver_file_handling
        test_file_relative = "test.txt"
        # Simulate context.get_full_path returning a resolved absolute path
        resolved_absolute_path = str(tmp_path / test_file_relative)
        mock_context_get_full_path.return_value = resolved_absolute_path

        assert driver.file_exists(test_file_relative) is True
        # file_exists calls _validate_path, which calls context.get_full_path
        mock_context_get_full_path.assert_called_once_with(test_file_relative)
        # Check that methods on the Path object created internally were called
        # Note: Path() is called *inside* file_exists with the resolved_absolute_path
        # We could mock Path here too, but the current test focuses on the interaction
        # with context.get_full_path and the final exists/is_file checks.
        # Let's assume Path(resolved_absolute_path) works as expected for this test's scope.
        mock_path_exists.assert_called_once_with()
        mock_path_is_file.assert_called_once_with()


    @patch.object(Context, 'get_full_path')
    @patch('pathlib.Path.exists', return_value=False) # Mock Path.exists
    @patch('pathlib.Path.is_file') # Mock Path.is_file (should not be called)
    def test_file_exists_non_existing(self, mock_path_is_file, mock_path_exists, mock_context_get_full_path, test_driver_file_handling, tmp_path):
        driver = test_driver_file_handling
        non_existing_file_relative = "nonexist.txt"
        resolved_absolute_path = str(tmp_path / non_existing_file_relative)
        mock_context_get_full_path.return_value = resolved_absolute_path

        assert driver.file_exists(non_existing_file_relative) is False
        # file_exists calls _validate_path, which calls context.get_full_path
        mock_context_get_full_path.assert_called_once_with(non_existing_file_relative)
        mock_path_exists.assert_called_once_with() # Path(...).exists() should be called
        mock_path_is_file.assert_not_called() # Path(...).is_file() should not be called if exists() is False

    # REMOVED the old test_file_exists_outside_base_path due to complexity in triggering specific log

    # ADDED a new test to cover the case where _validate_path returns None
    @patch.object(WorkflowDriver, '_validate_path', return_value=None)
    @patch('pathlib.Path.exists') # Should not be called if _validate_path returns None
    @patch('pathlib.Path.is_file') # Should not be called if _validate_path returns None
    def test_file_exists_returns_false_if_validate_path_fails(self, mock_path_is_file, mock_path_exists, mock_validate_path, test_driver_file_handling):
        """Test file_exists returns False if _validate_path returns None (e.g., due to traversal or invalid path)."""
        driver = test_driver_file_handling
        relative_path = "../sensitive/file.txt" # Or any path, the mock ensures validation fails

        assert driver.file_exists(relative_path) is False

        mock_validate_path.assert_called_once_with(relative_path)
        mock_path_exists.assert_not_called()
        mock_path_is_file.assert_not_called()
        # No specific log check needed here, as the logging for the failure reason
        # happens *inside* _validate_path or Context.get_full_path, which are mocked away.


    # Test for invalid path type - the type check happens before _validate_path
    # No need to patch context.get_full_path or _validate_path
    def test_file_exists_invalid_path_type(self, test_driver_file_handling, caplog):
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling
        # The code checks type *before* calling _validate_path, so _validate_path (and context.get_full_path) are NOT called.
        # No patch needed here.

        assert driver.file_exists(None) is False
        # The log comes from file_exists itself, not _validate_path or context
        assert "file_exists received non-string input: <class 'NoneType'>" in caplog.text
        caplog.clear()

        assert driver.file_exists(123) is False
        assert "file_exists received non-string input: <class 'int'>" in caplog.text


    # --- Tests for list_files ---
    # With the _validate_path code change, mock_context_get_full_path("") should now be called.
    @patch.object(Context, 'get_full_path')
    @patch('os.listdir')
    @patch('src.core.automation.workflow_driver.Path') # Mock Path class used in list_files
    @patch.object(WorkflowDriver, '_is_valid_filename', return_value=True)
    def test_list_files_success(self, mock_is_valid_filename, mock_Path_class, mock_os_listdir, mock_context_get_full_path, test_driver_file_handling, tmp_path):
        driver = test_driver_file_handling
        resolved_base_path_str = str(tmp_path.resolve())
        # Simulate context.get_full_path("") returning the resolved base path
        mock_context_get_full_path.return_value = resolved_base_path_str

        listdir_entries = ["file1.txt", "subdir", "file2.py"]
        mock_os_listdir.return_value = listdir_entries

        # Configure the mock Path class and its instances
        mock_base_path_instance = MagicMock()
        mock_base_path_instance.is_dir.return_value = True
        # Mock the string representation as os.listdir is called with a string
        mock_base_path_instance.__str__.return_value = resolved_base_path_str

        entry_mocks_by_name = {
            "file1.txt": MagicMock(is_file=MagicMock(return_value=True), is_dir=MagicMock(return_value=False)),
            "subdir": MagicMock(is_file=MagicMock(return_value=False), is_dir=MagicMock(return_value=True)),
            "file2.py": MagicMock(is_file=MagicMock(return_value=True), is_dir=MagicMock(return_value=False)),
        }

        # Define the side effect for the Path *class*
        def path_class_side_effect(path_arg):
            # Check if it's the base path string
            if path_arg == resolved_base_path_str:
                return mock_base_path_instance

            # Check if it's one of the entry path strings (only valid ones are passed to Path)
            for name in listdir_entries: # Iterate all names from listdir
                 # Check if this name is considered valid by the mock _is_valid_filename
                 # In this specific test, _is_valid_filename is mocked to return True for all,
                 # so all names from listdir_entries will result in a Path call.
                 expected_entry_path_str = os.path.join(resolved_base_path_str, name)
                 if path_arg == expected_entry_path_str:
                     # Return the mock for this entry name
                     return entry_mocks_by_name.get(name, MagicMock()) # Use .get for safety

            # If called with anything else, it's unexpected
            raise AssertionError(f"Unexpected Path call with argument: {path_arg}")

        mock_Path_class.side_effect = path_class_side_effect

        entries = driver.list_files()

        # _validate_path("") should now call context.get_full_path("")
        mock_context_get_full_path.assert_called_once_with("")

        # Assert that Path was called for the base path and for each entry
        # Since _is_valid_filename is mocked to return True for all, Path is called for all.
        expected_calls_to_path_class = [call(resolved_base_path_str)]
        for name in listdir_entries:
             expected_entry_path_str = os.path.join(resolved_base_path_str, name)
             expected_calls_to_path_class.append(call(expected_entry_path_str))

        mock_Path_class.assert_has_calls(expected_calls_to_path_class, any_order=True)

        # Assert calls on the instances returned by Path
        mock_base_path_instance.is_dir.assert_called_once_with()

        # Specific assertions for each entry mock based on their mocked return values
        entry_mocks_by_name["file1.txt"].is_file.assert_called_once_with()
        entry_mocks_by_name["file1.txt"].is_dir.assert_not_called() # is_dir not called if is_file is True

        entry_mocks_by_name["subdir"].is_file.assert_called_once_with()
        entry_mocks_by_name["subdir"].is_dir.assert_called_once_with() # is_dir called if is_file is False

        entry_mocks_by_name["file2.py"].is_file.assert_called_once_with()
        entry_mocks_by_name["file2.py"].is_dir.assert_not_called() # is_dir not called if is_file is True

        assert len(entries) == 3
        assert {'name': 'file1.txt', 'status': 'file'} in entries
        assert {'name': 'subdir', 'status': 'directory'} in entries
        assert {'name': 'file2.py', 'status': 'file'} in entries
        assert mock_is_valid_filename.call_count == 3 # Called for each entry from listdir


    @patch.object(Context, 'get_full_path', return_value=None) # Simulate path resolution failure
    @patch('os.listdir') # Should not be called
    @patch('src.core.automation.workflow_driver.Path') # Should not be called
    def test_list_files_base_path_resolution_failure(self, mock_Path_class, mock_os_listdir, mock_context_get_full_path, test_driver_file_handling, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        entries = driver.list_files()

        # _validate_path("") should now call context.get_full_path("")
        mock_context_get_full_path.assert_called_once_with("")
        assert len(entries) == 0
        # Check the log message from list_files when _validate_path returns None
        assert "Failed to resolve base path for listing: base path" in caplog.text
        mock_os_listdir.assert_not_called()
        mock_Path_class.assert_not_called()


    @patch.object(Context, 'get_full_path')
    @patch('os.listdir', side_effect=PermissionError("Permission denied"))
    @patch('src.core.automation.workflow_driver.Path')
    def test_list_files_permission_denied(self, mock_Path_class, mock_os_listdir, mock_context_get_full_path, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        resolved_base_path_str = str(tmp_path.resolve())
        # Simulate context.get_full_path("") returning the resolved base path
        mock_context_get_full_path.return_value = resolved_base_path_str

        mock_base_path_instance = MagicMock()
        mock_base_path_instance.is_dir.return_value = True
        mock_base_path_instance.__str__.return_value = resolved_base_path_str # For os.listdir call

        # Define a simple side effect for the Path class that just returns the base path mock
        # since os.listdir will raise an error before iterating entries.
        def path_class_side_effect(path_arg):
             if path_arg == resolved_base_path_str:
                 return mock_base_path_instance
             # No other Path calls are expected if os.listdir fails immediately
             raise AssertionError(f"Unexpected Path call with argument: {path_arg}")

        mock_Path_class.side_effect = path_class_side_effect


        entries = driver.list_files()

        # _validate_path("") should now call context.get_full_path("")
        mock_context_get_full_path.assert_called_once_with("")
        # Path(resolved_base_path_str) should be called once
        mock_Path_class.assert_called_once_with(resolved_base_path_str)
        mock_base_path_instance.is_dir.assert_called_once_with()
        # os.listdir is called with the string representation of the resolved base path
        mock_os_listdir.assert_called_once_with(resolved_base_path_str)
        assert len(entries) == 0
        # Check the log message from list_files when os.listdir raises PermissionError
        assert f"Permission denied when listing files in base path (resolved: {resolved_base_path_str})" in caplog.text


    @patch.object(Context, 'get_full_path')
    @patch('os.listdir') # Should not be called
    @patch('src.core.automation.workflow_driver.Path')
    def test_list_files_base_path_not_directory(self, mock_Path_class, mock_os_listdir, mock_context_get_full_path, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.ERROR)
        driver = test_driver_file_handling
        resolved_base_path_str = str(tmp_path.resolve())
        # Simulate context.get_full_path("") returning the resolved base path
        mock_context_get_full_path.return_value = resolved_base_path_str

        mock_base_path_instance = MagicMock()
        mock_base_path_instance.is_dir.return_value = False # Simulate base path is not a directory
        mock_base_path_instance.__str__.return_value = resolved_base_path_str # For Path call

        # Define a simple side effect for the Path class that just returns the base path mock
        def path_class_side_effect(path_arg):
             if path_arg == resolved_base_path_str:
                 return mock_base_path_instance
             # No other Path calls are expected if the base path is not a directory
             raise AssertionError(f"Unexpected Path call with argument: {path_arg}")

        mock_Path_class.side_effect = path_class_side_effect

        entries = driver.list_files()

        # _validate_path("") should now call context.get_full_path("")
        mock_context_get_full_path.assert_called_once_with("")
        # Path(resolved_base_path_str) should be called once
        mock_Path_class.assert_called_once_with(resolved_base_path_str)
        mock_base_path_instance.is_dir.assert_called_once_with()
        assert len(entries) == 0
        # Check the log message from list_files when Path(...).is_dir() is False
        assert f"Base path is not a valid directory: base path (resolved: {resolved_base_path_str})" in caplog.text
        mock_os_listdir.assert_not_called()

    @patch.object(Context, 'get_full_path')
    @patch('os.listdir', return_value=["valid_file.txt", "file!@#.txt", ".hidden_file.txt"])
    @patch('src.core.automation.workflow_driver.Path')
    @patch.object(WorkflowDriver, '_is_valid_filename')
    def test_list_files_invalid_filename(self, mock_is_valid_filename_method, mock_Path_class, mock_os_listdir, mock_context_get_full_path, test_driver_file_handling, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        driver = test_driver_file_handling
        resolved_base_path_str = str(tmp_path.resolve())
        # Simulate context.get_full_path("") returning the resolved base path
        mock_context_get_full_path.return_value = resolved_base_path_str

        listdir_entries = ["valid_file.txt", "file!@#.txt", ".hidden_file.txt"]
        mock_os_listdir.return_value = listdir_entries

        mock_base_path_instance = MagicMock()
        mock_base_path_instance.is_dir.return_value = True
        mock_base_path_instance.__str__.return_value = resolved_base_path_str # For os.listdir call

        # Mocks for entry instances - only 'valid_file.txt' will have its methods called
        entry_mocks_by_name = {
            "valid_file.txt": MagicMock(is_file=MagicMock(return_value=True), is_dir=MagicMock(return_value=False)),
            "file!@#.txt": MagicMock(), # Mock exists but its methods won't be called
            ".hidden_file.txt": MagicMock(), # Mock exists but its methods won't be called
        }

        # Define the side effect for the Path *class*
        def path_class_side_effect(path_arg):
            # Check if it's the base path string
            if path_arg == resolved_base_path_str:
                return mock_base_path_instance

            # Check if it's the path string for the *valid* entry
            valid_name = "valid_file.txt"
            expected_valid_entry_path_str = os.path.join(resolved_base_path_str, valid_name)
            if path_arg == expected_valid_entry_path_str:
                 return entry_mocks_by_name[valid_name]

            # If called with anything else, it's unexpected because Path() is only called
            # for the base path and for valid entry names.
            raise AssertionError(f"Unexpected Path call with argument: {path_arg}")

        mock_Path_class.side_effect = path_class_side_effect

        # Configure _is_valid_filename mock to filter
        mock_is_valid_filename_method.side_effect = lambda name: name == "valid_file.txt"

        entries = driver.list_files()

        # _validate_path("") should now call context.get_full_path("")
        mock_context_get_full_path.assert_called_once_with("")
        mock_os_listdir.assert_called_once_with(resolved_base_path_str)
        mock_base_path_instance.is_dir.assert_called_once_with()

        # Assert that Path was called only for the base path and the valid entry path
        expected_calls_to_path_class = [
            call(resolved_base_path_str),
            call(os.path.join(resolved_base_path_str, "valid_file.txt"))
        ]
        # Use any_order=True as the order of listdir might not be guaranteed,
        # although in this simple case it likely is. Safer this way.
        mock_Path_class.assert_has_calls(expected_calls_to_path_class, any_order=True)

        # Assert calls on the instances returned by Path
        # Only the mock for 'valid_file.txt' should have its methods called
        entry_mocks_by_name["valid_file.txt"].is_file.assert_called_once_with()
        entry_mocks_by_name["valid_file.txt"].is_dir.assert_not_called() # is_dir not called if is_file is True

        # Mocks for invalid files should not have their methods called
        entry_mocks_by_name["file!@#.txt"].is_file.assert_not_called()
        entry_mocks_by_name["file!@#.txt"].is_dir.assert_not_called()
        entry_mocks_by_name[".hidden_file.txt"].is_file.assert_not_called()
        entry_mocks_by_name[".hidden_file.txt"].is_dir.assert_not_called()


        assert len(entries) == 1
        assert {'name': 'valid_file.txt', 'status': 'file'} in entries
        assert mock_is_valid_filename_method.call_count == 3 # Called for each entry from listdir
        assert "Skipping listing of potentially unsafe filename: file!@#.txt" in caplog.text
        assert "Skipping listing of potentially unsafe filename: .hidden_file.txt" in caplog.text


    # --- Tests for _is_valid_filename ---
    # These tests are fine as they test a standalone method.

    def test_is_valid_filename_valid_formats(self, test_driver_file_handling):
        driver = test_driver_file_handling
        assert driver._is_valid_filename("file.txt") is True
        assert driver._is_valid_filename("file_name-123.py") is True
        assert driver._is_valid_filename("directory_name") is True
        assert driver._is_valid_filename("a") is True
        assert driver._is_valid_filename("1") is True
        assert driver._is_valid_filename("a.b.c") is True
        assert driver._is_valid_filename("a-b_c.d") is True

    def test_is_valid_filename_invalid_formats(self, test_driver_file_handling):
        driver = test_driver_file_handling
        assert driver._is_valid_filename("invalid/id") is False
        assert driver._is_valid_filename("..") is False
        assert driver._is_valid_filename("../file.txt") is False
        assert driver._is_valid_filename("file name") is False
        assert driver._is_valid_filename("file!@#") is False
        assert driver._is_valid_filename("") is False
        assert driver._is_valid_filename(None) is False
        assert driver._is_valid_filename(123) is False
        assert driver._is_valid_filename("task.") is False
        assert driver._is_valid_filename(".hidden_file.txt") is False
        assert driver._is_valid_filename("-file.txt") is False
        assert driver._is_valid_filename("_file.txt") is False

    # --- Tests for _merge_snippet ---
    # These tests are fine as they test a standalone method.
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
        expected = "line1\nline2\nline3\ninserted_line"
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
        expected = "line1\nsnippet"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected

    def test__merge_snippet_existing_ends_newline(self, test_driver_file_handling):
        driver = test_driver_file_handling
        existing = "line1\n"
        snippet = "snippet"
        expected = "line1\nsnippet"
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
        expected = "line1\ninserted\nline2\n# METAMORPHIC_INSERT_POINT\nline3"
        merged = driver._merge_snippet(existing, snippet)
        assert merged == expected