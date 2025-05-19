# tests/test_workflow_context.py

import pytest
import os
from src.core.automation.workflow_driver import Context
from pathlib import Path
import logging
from unittest.mock import patch # Import patch

# Set up logging for tests
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Fixture for a Context instance
@pytest.fixture
def test_context(tmp_path):
    return Context(str(tmp_path))

class TestContext:
    def test_context_initialization(self, tmp_path):
        base_path = str(tmp_path)
        context = Context(base_path)
        assert context.base_path == base_path
        assert context._resolved_base_path == Path(base_path).resolve()

    def test_context_initialization_invalid_path(self, caplog):
        caplog.set_level(logging.ERROR)
        # Simulate an invalid path that resolve() might fail on (e.g., non-existent drive letter on Windows)
        # This is hard to simulate portably, so we'll rely on mocking Path.resolve
        with patch('pathlib.Path.resolve', side_effect=Exception("Mock resolution error")):
            context = Context("/invalid/path")
            assert context.base_path == "/invalid/path"
            assert context._resolved_base_path is None
            assert "Error resolving base path" in caplog.text

    def test_context_get_full_path_valid(self, test_context, tmp_path):
        relative_path = "subdir/file.txt"
        expected_path = str((tmp_path / relative_path).resolve())
        full_path = test_context.get_full_path(relative_path)
        assert full_path == expected_path

    def test_context_get_full_path_relative_traversal(self, test_context, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        # Attempt to traverse outside the base directory
        relative_path = "../sensitive/file.txt"
        full_path = test_context.get_full_path(relative_path)
        assert full_path is None
        assert "Path traversal attempt detected during resolution" in caplog.text

    def test_context_get_full_path_absolute_traversal(self, test_context, tmp_path, caplog):
        caplog.set_level(logging.WARNING)
        # Attempt to access an absolute path outside the base directory
        absolute_path = "/tmp/sensitive_file.txt" # Use a common temp dir path
        full_path = test_context.get_full_path(absolute_path)
        assert full_path is None
        assert "Path traversal attempt detected during resolution" in caplog.text

    def test_context_get_full_path_empty_string(self, test_context, tmp_path):
        # Empty string should resolve to the base path itself
        expected_path = str(Path(str(tmp_path)).resolve())
        full_path = test_context.get_full_path("")
        assert full_path == expected_path

    def test_context_get_full_path_none(self, test_context, caplog):
        caplog.set_level(logging.WARNING)
        full_path = test_context.get_full_path(None)
        assert full_path is None
        # FIX: Update assertion to match the new log message format
        assert f"Attempted to resolve path with invalid input type: {type(None)}" in caplog.text

    def test_context_get_full_path_invalid_type(self, test_context, caplog):
        caplog.set_level(logging.WARNING)
        full_path = test_context.get_full_path(123)
        assert full_path is None
        # FIX: Update assertion to match the new log message format
        assert f"Attempted to resolve path with invalid input type: {type(123)}" in caplog.text

    def test_context_equality(self, tmp_path):
        context1 = Context(str(tmp_path))
        context2 = Context(str(tmp_path))
        context3 = Context(str(tmp_path / "another_dir"))

        assert context1 == context2
        assert context1 != context3
        assert context1 != "not a context"

    def test_context_repr(self, tmp_path):
        base_path = str(tmp_path)
        context = Context(base_path)
        assert repr(context) == f"Context(base_path='{base_path}')"