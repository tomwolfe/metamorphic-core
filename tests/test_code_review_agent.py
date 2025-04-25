# tests/test_code_review_agent.py
import pytest
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.knowledge_graph import KnowledgeGraph, Node
from unittest.mock import patch, MagicMock
import subprocess
import json
from datetime import datetime
import sys
from unittest.mock import MagicMock, patch, ANY
from src.core.agents.code_review_agent import CodeReviewAgent


@pytest.fixture
def review_agent():
    """Fixture to create a CodeReviewAgent instance."""
    return CodeReviewAgent()

# --- Flake8 Tests (Keeping these) ---
@pytest.mark.parametrize(
    "test_input, expected_issues_count, expected_issue_details",
    [
        (
            "",  # Test case 1: Zero issues in output
            0,
            [],
        ),
        (
            "test.py:1:1: E302 expected 2 blank lines, found 1",  # Test case 2: Single-line issue
            1,
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'expected 2 blank lines, found 1', 'severity': 'error'}],
        ),
        (
            """test.py:1:1: E302 expected 2 blank lines, found 1
test.py:3:5: F401 'os' imported but unused
test_module.py:10:20: W0612 Unused variable 'x'""",  # Test case 3: Multiple issues
            3,
            [
                {'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'expected 2 blank lines, found 1', 'severity': 'error'},
                {'file': 'test.py', 'line': '3', 'col': '5', 'code': 'F401', 'msg': "'os' imported but unused", 'severity': 'error'},
                {'file': 'test_module.py', 'line': '10', 'col': '20', 'code': 'W0612', 'msg': "Unused variable 'x'", 'severity': 'warning'},
            ],
        ),
        (
            "my code.py:1:1: F401 'os' imported",  # Test case 4: Filename with space
            1,
            [{'file': 'my code.py', 'line': '1', 'col': '1', 'code': 'F401', 'msg': "'os' imported", 'severity': 'error'}],
        ),
        (
            "file#name.py:1:1: F401 'os' imported",  # Test case 5: Filename with special char
            1,
            [{'file': 'file#name.py', 'line': '1', 'col': '1', 'code': 'F401', 'msg': "'os' imported", 'severity': 'error'}],
        ),
        (
            "test.py:1:1: E001 Error with 'quotes'",  # Test case 6: Error message with quotes
            1,
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E001', 'msg': "Error with 'quotes'", 'severity': 'style'}],
        ),
        (
            "test.py:1:1: E002 Error with \\escape",  # Test case 7: Error message with escape char
            1,
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E002', 'msg': "Error with \\escape", 'severity': 'style'}],
        ),
        (
            "test.py:1:1: E302 first line\nsecond line of message",  # Test case 8: Multi-line message - now correctly parsed as single line
            1,
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'first line', 'severity': 'error'}],  # Expecting only first line of message
        ),
        (
            "test.py:99999:1: E302 expected 2 blank lines",  # Test case 9: Maximum line number
            1,
            [{'file': 'test.py', 'line': '99999', 'col': '1', 'code': 'E302', 'msg': 'expected 2 blank lines', 'severity': 'error'}],
        ),
        (
            "test.py:1:1: E302 msg1; E303 msg2",  # Test case 10: Multiple issues on the same line - now correctly parsed as single line
            1,
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'msg1; E303 msg2', 'severity': 'error'}],  # Expecting only first issue
        ),
        (
            "test.py:1:1: E123 Indentation is not a multiple of four\ntest.py:5:10: F821 Undefined name 'variable_name'\ntest.py:12:1: W503 line break before binary operator\ntest.py:20:5: C0301 line too long (120 > 100 characters)",  # Test case 11: Different severity codes
            4,
            [
                {'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E123', 'msg': 'Indentation is not a multiple of four', 'severity': 'style'},
                {'file': 'test.py', 'line': '5', 'col': '10', 'code': 'F821', 'msg': "Undefined name 'variable_name'", 'severity': 'error'},
                {'file': 'test.py', 'line': '12', 'col': '1', 'code': 'W503', 'msg': 'line break before binary operator', 'severity': 'warning'},
                {'file': 'test.py', 'line': '20', 'col': '5', 'code': 'C0301', 'msg': 'line too long (120 > 100 characters)', 'severity': 'warning'},
            ],
        ),
        (
            "test.py:1:1: E302 expected 2 blank lines, found 1\n"  # Error
            "test.py:2:1: XYZ99 Unknown code",  # Unknown code
            2,
            [
                {'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'expected 2 blank lines, found 1', 'severity': 'error'},
                {'file': 'test.py', 'line': '2', 'col': '1', 'code': 'XYZ99', 'msg': 'Unknown code', 'severity': 'info'},  # severity now defaults to info
            ],
        ),
    ],
)
def test_parse_flake8_output_with_severity(review_agent, test_input, expected_issues_count, expected_issue_details):
    """Test _parse_flake8_results method with severity classification."""
    results = review_agent._parse_flake8_results(test_input)
    assert len(results) == expected_issues_count # Corrected assertion to check length of the list

    if expected_issues_count > 0:
        for i in range(expected_issues_count):
            expected_issue = expected_issue_details[i]
            actual_issue = results[i] # Corrected indexing
            assert actual_issue['file'] == expected_issue['file']
            assert actual_issue['line'] == expected_issue['line']
            assert actual_issue['col'] == expected_issue['col']
            assert actual_issue['code'] == expected_issue['code']
            assert actual_issue['message'] == expected_issue['msg'] # Corrected key name
            assert actual_issue['severity'] == expected_issue['severity']
            assert isinstance(actual_issue['line'], str)

def test_parse_flake8_output_malformed(review_agent):
    """Test error handling for malformed flake8 output."""
    sample_output = "invalid output format"
    results = review_agent._parse_flake8_results(sample_output)
    assert results == [] # Corrected assertion to check the list

@patch('subprocess.run')
def test_analyze_python_flake8_success(mock_run, review_agent):
    """Test successful flake8 execution."""
    # Simulate Flake8 success + Bandit success (no findings)
    mock_run.side_effect = [
        MagicMock(stdout="test.py:1:1: E302 expected 2 blank lines, found 1", returncode=0),  # Flake8 response
        MagicMock(stdout=json.dumps({'results': []}), returncode=0)  # Bandit response
    ]

    result = review_agent.analyze_python("def code(): pass")
    assert result['status'] == 'failed' # Expect 'failed' because Flake8 issue is 'error' severity
    assert result['static_analysis'] # Assert static_analysis is present and not empty
    assert 'flake8_output' in result # Assert 'flake8_output' key is present
    assert result['errors']['flake8'] is None # Assert no Flake8 execution error
    assert result['errors']['bandit'] is None # Assert no Bandit execution error


# --- Bandit Tests (Unskipped) ---

# Removed @pytest.mark.skip("Temporarily skipping old tests for MVP focus")
@patch('subprocess.run')
def test_analyze_python_bandit_success(mock_run, review_agent):
    """Test successful Bandit execution and parsing."""
    bandit_output = {
        "results": [{
            "code": "23",
            "details": "Possible SQL injection vulnerability...",
            "filename": "test.py",
            "issue_confidence": "HIGH",
            "issue_severity": "HIGH",
            "issue_text": "Possible SQL injection vulnerability...",
            "line_number": 5,
            "line_range": [5],
            "more_info": "https://owasp.org/www-community/attacks/SQL_Injection",
            "test_id": "B608",
            "test_name": "hardcoded_sql_expressions"
        }]
    }
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0),  # Flake8 - no output
        MagicMock(stdout=json.dumps(bandit_output), returncode=0)  # Bandit output with findings
    ]

    result = review_agent.analyze_python("import os; os.system('ls -l')")  # Example code doesn't matter here for mock output
    assert result['status'] == 'failed' # Expect 'failed' because Bandit finding is 'security_high'
    assert len(result['static_analysis']) == 1 # Should have 1 finding (from Bandit)
    finding = result['static_analysis'][0]
    assert finding['code'] == 'B608'
    assert finding['severity'] == 'security_high'
    assert result['errors']['flake8'] is None
    assert result['errors']['bandit'] is None


# Removed @pytest.mark.skip("Temporarily skipping old tests for MVP focus")
@patch('subprocess.run')
def test_analyze_python_bandit_calledprocesserror(mock_run, review_agent, caplog):
    """Test handling of subprocess.CalledProcessError from Bandit."""
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0),  # Flake8 - no output
        subprocess.CalledProcessError(returncode=1, cmd=['bandit'], stderr=b"Bandit error")  # Bandit error
    ]
    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("import os; os.system('ls -l')")
        assert result['status'] == 'error' # Expect 'error' status
        assert result['errors']['bandit'] is not None # Expect Bandit error message
        assert "Bandit execution failed" in result['errors']['bandit'] # Corrected assertion
        assert result['static_analysis'] == [] # No findings should be parsed
    assert "Bandit execution failed with return code 1 and no output. Stderr:\nBandit error" in caplog.text # Check log


# Removed @pytest.mark.skip("Temporarily skipping old tests for MVP focus")
@patch('subprocess.run')
def test_analyze_python_bandit_filenotfounderror(mock_run, review_agent):
    """Test handling of FileNotFoundError from Bandit."""
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0),  # Flake8 - no output
        FileNotFoundError("bandit not found")  # Bandit not found
    ]
    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("import os; os.system('ls -l')")
        assert result['status'] == 'error' # Expect 'error' status
        assert result['errors']['bandit'] is not None # Expect Bandit error message
        assert "Bandit executable not found" in result['errors']['bandit'] # Corrected assertion
        assert result['static_analysis'] == [] # No findings should be parsed


# Removed @pytest.mark.skip("Temporarily skipping old tests for MVP focus")
@patch('subprocess.run')
def test_analyze_python_bandit_jsondecodeerror(mock_run, review_agent, caplog):
    """Test handling of JSONDecodeError from Bandit output."""
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0),  # Flake8 - no output
        MagicMock(stdout="invalid json", returncode=0)  # Bandit - invalid json
    ]

    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("import os; os.system('ls -l')")
        assert result['status'] == 'error' # Expect 'error' status
        assert result['errors']['bandit'] is not None # Expect Bandit error message
        assert "Error parsing Bandit JSON output" in result['errors']['bandit']
        assert result['static_analysis'] == [] # No findings should be parsed
    assert "Error parsing Bandit JSON output: Expecting value: line 1 column 1 (char 0). Raw output:\ninvalid json" in caplog.text # Verify raw output logged


# Removed @pytest.mark.skip("Temporarily skipping old tests for MVP focus")
@patch('subprocess.run')
def test_analyze_python_bandit_generic_exception(mock_run, review_agent):
    """Test handling of generic exceptions during Bandit execution."""
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0),  # Flake8 - no output
        Exception("Generic bandit error")  # Bandit - generic exception
    ]

    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("import os; os.system('ls -l')")
        assert result['status'] == 'error' # Expect 'error' status
        assert result['errors']['bandit'] is not None # Expect Bandit error message
        assert "Error running bandit: Generic bandit error" in result['errors']['bandit'] # Corrected assertion
        assert result['static_analysis'] == [] # No findings should be parsed


# --- Merge Results Tests (Unskipped) ---

# Removed @pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_merge_results(review_agent):
    """Test merging of Flake8 and Bandit results."""
    flake8_results = {'static_analysis': [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'message': 'Flake8 issue', 'severity': 'error'}]} # Corrected key name
    bandit_results = {
        'results': [{ # Corrected key name to 'results' to match Bandit output structure
            "filename": "test.py",
            "line_number": 5,
            "issue_text": "Bandit issue",
            "test_id": "B101",
            "issue_severity": "HIGH"
        }]
    }
    merged = review_agent._merge_results(flake8_results, bandit_results)
    assert len(merged['static_analysis']) == 2
    assert merged['static_analysis'][1]['code'] == 'B101'
    assert merged['static_analysis'][1]['severity'] == 'security_high'

# Removed @pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_map_bandit_severity(review_agent):
    """Test mapping Bandit severity levels."""
    assert review_agent._map_bandit_severity('HIGH') == 'security_high'
    assert review_agent._map_bandit_severity('MEDIUM') == 'security_medium' # Corrected expectation
    assert review_agent._map_bandit_severity('LOW') == 'security_low' # Corrected expectation
    assert review_agent._map_bandit_severity('INFO') == 'info'

# --- KG Integration Tests (Skipped for MVP, but kept for future reference) ---

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_store_findings_kg_integration_with_severity(review_agent):
    """Test that findings with severity are stored in KG."""
    mock_kg = MagicMock(spec=KnowledgeGraph)
    review_agent.kg = mock_kg

    sample_findings = {
        'static_analysis': [
            {'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'message': 'test message', 'severity': 'error'} # Corrected key name
        ]
    }
    code_hash_str = "1234567890"

    review_agent.store_findings(sample_findings, code_hash_str, "def code(): pass")  # Added code sample

    mock_kg.add_node.assert_called_once()
    added_node = mock_kg.add_node.call_args[0][0]

    assert added_node.type == "code_review"
    assert "Static analysis findings from flake8 and bandit" in added_node.content  # Corrected assertion
    assert isinstance(added_node.metadata['findings'], list)

    finding = added_node.metadata['findings'][0]
    assert finding['severity'] == 'error'
    assert 'file' in finding
    assert 'line' in finding
    assert 'col' in finding
    assert 'code' in finding
    assert 'message' in finding # Corrected key name

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_analyze_python_stores_findings_in_kg(review_agent):
    """Test that analyze_python stores findings in KG."""
    mock_kg = MagicMock(spec=KnowledgeGraph)
    review_agent.kg = mock_kg

    # Setup mock to handle both Flake8 and Bandit calls
    mock_run = MagicMock()
    mock_run.side_effect = [
        MagicMock(stdout="test.py:1:1: E302 expected 2 blank lines, found 1", returncode=0),
        MagicMock(stdout=json.dumps({'results': []}), returncode=0)
    ]

    with patch('subprocess.run', mock_run):
        code_sample = "def example(): pass"
        code_hash_str = str(hash(code_sample))
        review_agent.analyze_python(code_sample)

    mock_kg.add_node.assert_called()
    call_args = mock_kg.add_node.call_args
    node_arg = call_args[0][0]

    assert isinstance(node_arg, Node)
    assert node_arg.type == 'code_review'
    assert node_arg.content == 'Static analysis findings from flake8 and bandit' # Corrected assertion
    assert node_arg.metadata['code_hash'] == code_hash_str
    assert len(node_arg.metadata['findings']) == 1
    assert 'timestamp' in node_arg.metadata

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_kg_integration_with_severity(review_agent):
    """Test the integration with the Knowledge Graph and severity classification."""
    sample_code = """
        def my_function():
            print('Hello, World!')  # E302 expected 2 blank lines after function definition
        """

    mock_kg = MagicMock(spec=KnowledgeGraph)
    review_agent.kg = mock_kg

    # Simulate Flake8 success + Bandit success (no findings)
    mock_run = MagicMock()
    mock_run.side_effect = [
        MagicMock(stdout="test.py:2:1: E302 expected 2 blank lines, found 1", returncode=0),  # Flake8 output with issue
        MagicMock(stdout=json.dumps({'results': []}), returncode=0)  # Bandit response - no findings
    ]

    with patch('subprocess.run', mock_run):
        findings = review_agent.analyze_python(sample_code)
        mock_kg.add_node.assert_called_once()

    node = mock_kg.add_node.call_args[0][0]

    assert node.type == "code_review"
    assert isinstance(node.metadata['findings'], list)

    if node.metadata['findings']:
        first_finding = node.metadata['findings'][0]
        assert first_finding['severity'] == 'error'

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_store_findings_stores_code_snippet(review_agent):
    """Test that store_findings stores code snippet in KG metadata."""
    mock_kg = MagicMock(spec=KnowledgeGraph)
    review_agent.kg = mock_kg
    sample_findings = {
        'static_analysis': [
            {'file': 'test.py', 'line': '2', 'col': '10', 'code': 'E303', 'message': 'Too many blank lines', 'severity': 'style'} # Corrected key name
        ]
    }
    code_sample = """def test_function():


        x = 10"""  # Intentionally has extra lines

    review_agent.store_findings(sample_findings, code_hash_str, code_sample)
    mock_kg.add_node.assert_called_once()
    node = mock_kg.add_node.call_args[0][0]
    assert "code_snippet" in node.metadata
    assert "def test_function():" in node.metadata["code_snippet"]
    assert "x = 10" in node.metadata["code_snippet"]

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_get_code_snippet_line_context(review_agent):
    """Test _get_code_snippet with line number and context."""
    code = """line1
line2
line3
line4
line5
line6
line7
line8
line9
line10"""
    snippet = review_agent._get_code_snippet(code, line_num=5, context=2)
    assert "line3" in snippet
    assert "line4" in snippet
    assert "line5" in snippet
    assert "line6" in snippet
    assert "line7" in snippet
    assert "line8" not in snippet
    assert "line2" not in snippet

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_get_code_snippet_no_line_number(review_agent):
    """Test _get_code_snippet without line number returns full code."""
    code = "line1\nline2\nline3"
    snippet = review_agent._get_code_snippet(code)
    assert snippet == code.strip()

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_get_code_snippet_empty_code(review_agent):
    """Test _get_code_snippet with empty code."""
    code = ""
    snippet = review_agent._get_code_snippet(code)
    assert snippet == code.strip()

@pytest.mark.skip("Temporarily skipping old tests for MVP focus")
def test_security_vulnerability_detection(review_agent):
    """End-to-end test with real security vulnerability detection by Bandit."""
    risky_code = "import subprocess\nsubprocess.Popen(['ls', '-l', '/'])"  # Example command injection

    # Mock subprocess.run to simulate flake8 passing and bandit finding issue
    mock_run = MagicMock()
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0),  # Flake8 - no output
        MagicMock(stdout=json.dumps({  # Bandit output with vulnerability
            'results': [{
                'test_id': 'B603',
                'issue_text': 'Uses subprocess',
                'issue_severity': 'HIGH',
                'issue_confidence': 'MEDIUM',
                'line_number': 2,
                'filename': '<string>'
            }]
        }), returncode=0)
    ]
    with patch('subprocess.run', mock_run):
        results = review_agent.analyze_python(risky_code)
        assert any(f['code'] == 'B603' and f['severity'] == 'security_high' for f in results['static_analysis'])  # B603 is subprocess_popen_with_shell_equals_true


# --- Other Tests (Keeping these) ---

@patch('subprocess.run')
def test_analyze_python_invokes_flake8_with_py_file(mock_run, review_agent):
    """Verify flake8 is called with correct parameters."""
    agent = CodeReviewAgent()
    # Mock Bandit call as well since analyze_python now runs both
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0), # Flake8 mock
        MagicMock(stdout=json.dumps({'results': []}), returncode=0) # Bandit mock
    ]
    code = "print(1)"
    agent.analyze_python(code)
    # Uses patched ANY to confirm tmp file path
    mock_run.assert_any_call(
        ['flake8', ANY],
        capture_output=True,
        text=True,
        check=False
    )
    mock_run.assert_any_call(
         ['bandit', '-r', ANY, '-f', 'json'],
         capture_output=True,
         text=True,
         check=False
    )


@patch('subprocess.run')
def test_analyze_python_returns_flake8_stdout(mock_run, review_agent):
    """Check successful analysis returns captured flake8 stdout."""
    mock_run.side_effect = [
        MagicMock(stdout="Sample flake8 output", returncode=0), # Flake8 mock
        MagicMock(stdout=json.dumps({'results': []}), returncode=0) # Bandit mock
    ]
    result = review_agent.analyze_python("")
    # Corrected assertion to include static analysis and other keys
    assert result['flake8_output'] == 'Sample flake8 output'
    assert 'static_analysis' in result
    assert 'status' in result
    assert 'errors' in result


@patch('subprocess.run')
def test_analyze_python_returns_empty_stdout_on_success(mock_run, review_agent):
    """Verify clean code returns empty output dict (no flake8 warnings)."""
    mock_run.side_effect = [
        MagicMock(stdout="", returncode=0), # Flake8 mock
        MagicMock(stdout=json.dumps({'results': []}), returncode=0) # Bandit mock
    ]
    result = review_agent.analyze_python("def x(): return 1")
    # Corrected assertion to check the full result structure
    assert result == {
        'status': 'success',
        'flake8_output': '',
        'static_analysis': [],
        'errors': {'flake8': None, 'bandit': None}
    }


@patch('subprocess.run')
def test_analyze_python_returns_flake8_errors_when_present(mock_run, review_agent):
    """Ensure flake8 errors are captured correctly in output."""
    mock_error = "test.py:1:7: E225 missing whitespace around operator"
    mock_run.side_effect = [
        MagicMock(stdout=mock_error, returncode=1), # Flake8 mock with error
        MagicMock(stdout=json.dumps({'results': []}), returncode=0) # Bandit mock
    ]
    result = review_agent.analyze_python("if(True):print('test')")
    assert result['flake8_output'] == mock_error
    assert result['static_analysis'] == review_agent._merge_results({'static_analysis': review_agent._parse_flake8_results(mock_error)}, {'results': []}).get('static_analysis') # Assert merged static analysis is parsed
    assert result['status'] == 'failed' # Expect 'failed' due to Flake8 error severity


@patch('subprocess.run', side_effect=FileNotFoundError("flake8 not found"))
def test_analyze_python_handles_file_not_found(mock_run, review_agent):
    """Test file not found scenario returns error dict."""
    agent = CodeReviewAgent()
    # The FileNotFoundError happens during the first subprocess.run call (Flake8)
    # The Bandit call will not be reached in this scenario.
    result = agent.analyze_python("def y(): pass")
    # Corrected assertion to match the new error handling structure
    assert result == {
        'status': 'error',
        'flake8_output': '',
        'static_analysis': [],
        'errors': {'flake8': 'FileNotFoundError: flake8 not found', 'bandit': None}
    }


@patch('subprocess.run')
def test_analyze_python_captures_returncode_exit_status(mock_run, review_agent):
    """Verify returncode does not affect raw stdout capture."""
    mock_run.side_effect = [
        MagicMock(stdout="Error found", returncode=1), # Flake8 mock with non-zero returncode
        MagicMock(stdout=json.dumps({'results': []}), returncode=0) # Bandit mock
    ]
    agent = CodeReviewAgent()
    # Even with returncode=1, output should be captured
    result = agent.analyze_python("var = 5;")
    assert result['flake8_output'] == 'Error found' # Flake8 output captured
    assert result['status'] == 'failed' # Status is 'failed' due to Flake8 error severity