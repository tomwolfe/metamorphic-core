import pytest
import sys
from unittest.mock import MagicMock, patch, ANY
from src.core.agents.code_review_agent import CodeReviewAgent

def test_analyze_python_invokes_flake8_with_py_file():
    """Verify flake8 is called with correct parameters."""
    agent = CodeReviewAgent()
    with patch('subprocess.run') as mock_run:
        code = "print(1)"
        agent.analyze_python(code)
        # Uses patched ANY to confirm tmp file path
        mock_run.assert_called_with(
            ['flake8', ANY],
            capture_output=True,
            text=True,
            check=False
        )

def test_analyze_python_returns_flake8_stdout():
    """Check successful analysis returns captured flake8 stdout."""
    mock_result = MagicMock()
    mock_result.stdout = "Sample flake8 output"
    with patch('subprocess.run', return_value=mock_result):
        result = CodeReviewAgent().analyze_python("")
    assert result == {'output': 'Sample flake8 output'}

def test_analyze_python_returns_empty_stdout_on_success():
    """Verify clean code returns empty output dict (no flake8 warnings)."""
    with patch('subprocess.run', return_value=MagicMock(stdout="", returncode=0)):
        result = CodeReviewAgent().analyze_python("def x(): return 1")
    assert result['output'] == ""

def test_analyze_python_returns_flake8_errors_when_present():
    """Ensure flake8 errors are captured correctly in output."""
    mock_error = "test.py:1:7: E225 missing whitespace around operator"
    with patch('subprocess.run', return_value=MagicMock(stdout=mock_error, returncode=1)):
        result = CodeReviewAgent().analyze_python("if(True):print('test')")
    assert result['output'] == mock_error

def test_analyze_python_handles_file_not_found():
    """Test file not found scenario returns error dict."""
    agent = CodeReviewAgent()
    with patch('subprocess.run', side_effect=FileNotFoundError("flake8 not found")):
        # Expected return when flake8 is missing
        result = agent.analyze_python("def y(): pass")
    assert result == {'error': "FileNotFoundError: flake8 not found"}

def test_analyze_python_captures_returncode_exit_status():
    """Verify returncode does not affect raw stdout capture."""
    agent = CodeReviewAgent()
    mock_result = MagicMock(stdout="Error found", returncode=1)
    with patch('subprocess.run', return_value=mock_result):
        # Even with returncode=1, output should be captured
        result = CodeReviewAgent().analyze_python("var = 5;")
        assert 'output' in result
        assert result['output'] == "Error found"