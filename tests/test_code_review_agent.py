# tests/test_code_review_agent.py
import pytest
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.knowledge_graph import KnowledgeGraph, Node
from unittest.mock import patch, MagicMock
import subprocess
from datetime import datetime

@pytest.fixture
def review_agent():
    """Fixture to create a CodeReviewAgent instance with an in-memory KnowledgeGraph."""
    return CodeReviewAgent(KnowledgeGraph())

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
                {'file': 'test.py', 'line': '3', 'col': '5', 'code': 'F401', 'msg': "'os' imported but unused", 'severity': 'error'}, # Assuming F401 is also 'error' for simplicity in example
                {'file': 'test_module.py', 'line': '10', 'col': '20', 'code': 'W0612', 'msg': "Unused variable 'x'", 'severity': 'warning'}, # Assuming W0612 is 'warning'
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
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E001', 'msg': "Error with 'quotes'", 'severity': 'info'}], # Default severity 'info' for unknown codes
        ),
        (
            "test.py:1:1: E002 Error with \\escape",  # Test case 7: Error message with escape char
            1,
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E002', 'msg': "Error with \\escape", 'severity': 'info'}], # Default severity 'info' for unknown codes
        ),
        (
            "test.py:1:1: E302 first line\nsecond line of message",  # Test case 8: Multi-line message (flake8 usually doesn't do this, but testing robustness)
            1,
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'first line', 'severity': 'error'}], # Adjusted: Expect only the first line of the message
        ),
        (
            "test.py:99999:1: E302 expected 2 blank lines",  # Test case 9: Maximum line number
            1,
            [{'file': 'test.py', 'line': '99999', 'col': '1', 'code': 'E302', 'msg': 'expected 2 blank lines', 'severity': 'error'}],
        ),
        (
            "test.py:1:1: E302 msg1; E303 msg2", # Test case 10: Multiple issues on the same line (flake8 doesn't do this, but testing robustness)
            1, # Current parser expects one issue per line
            [{'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'msg1; E303 msg2', 'severity': 'error'}], # Parser will capture the whole line as one message
        ),
        (
            "test.py:1:1: E123 Indentation is not a multiple of four\ntest.py:5:10: F821 Undefined name 'variable_name'\ntest.py:12:1: W503 line break before binary operator\ntest.py:20:5: C0301 line too long (120 > 100 characters)",  # Test case 11: Different severity codes
            4,
            [
                {'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E123', 'msg': 'Indentation is not a multiple of four', 'severity': 'style'}, # E123 -> style
                {'file': 'test.py', 'line': '5', 'col': '10', 'code': 'F821', 'msg': "Undefined name 'variable_name'", 'severity': 'error'}, # F821 -> error
                {'file': 'test.py', 'line': '12', 'col': '1', 'code': 'W503', 'msg': 'line break before binary operator', 'severity': 'warning'}, # W503 -> warning
                {'file': 'test.py', 'line': '20', 'col': '5', 'code': 'C0301', 'msg': 'line too long (120 > 100 characters)', 'severity': 'warning'}, # C0301 -> warning (or style, adjust severity_map if needed)
            ],
        ),
         (
            "test.py:1:1: E302 expected 2 blank lines, found 1\n"  # Error
            "test.py:2:1: XYZ99 Unknown code", # Unknown code - should default to 'info'
            2,
            [
                {'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'expected 2 blank lines, found 1', 'severity': 'error'},
                {'file': 'test.py', 'line': '2', 'col': '1', 'code': 'XYZ99', 'msg': 'Unknown code', 'severity': 'info'}, # Unknown defaults to 'info'
            ],
        ),
    ],
)
def test_parse_flake8_output_with_severity(review_agent, test_input, expected_issues_count, expected_issue_details):
    """Test _parse_results method with severity classification."""
    results = review_agent._parse_results(test_input)
    assert len(results['static_analysis']) == expected_issues_count

    if expected_issues_count > 0:
        for i in range(expected_issues_count):
            expected_issue = expected_issue_details[i]
            actual_issue = results['static_analysis'][i]
            assert actual_issue['file'] == expected_issue['file']
            assert actual_issue['line'] == expected_issue['line']
            assert actual_issue['col'] == expected_issue['col']
            assert actual_issue['code'] == expected_issue['code']
            assert actual_issue['msg'] == expected_issue['msg']
            assert actual_issue['severity'] == expected_issue['severity'] # Assert severity
            assert isinstance(actual_issue['line'], str)

def test_parse_flake8_output_malformed(review_agent):
    """Test error handling for malformed flake8 output that doesn't match the expected pattern."""
    sample_output = "invalid output format - no colon separators"
    results = review_agent._parse_results(sample_output)
    assert results['static_analysis'] == [] # Should gracefully handle malformed output and return empty list

def test_analyze_python_flake8_success(review_agent):
    """Test successful execution of flake8."""
    mock_run = MagicMock()
    mock_run.return_value.stdout = "test.py:1:1: E302 expected 2 blank lines, found 1"
    mock_kg = MagicMock(spec=KnowledgeGraph)  # Mock KnowledgeGraph here!
    review_agent.kg = mock_kg # Inject mock KG

    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("def code(): pass")
        assert 'error' not in result # Now assert 'error' is NOT in the result
        assert len(result['static_analysis']) == 1 # Assert findings are parsed
        # Optionally, add assertions to check the content of result['static_analysis'] if needed

def test_analyze_python_flake8_calledprocesserror(review_agent, caplog):  # Inject caplog fixture
    """Test handling of subprocess.CalledProcessError from flake8."""
    mock_run = MagicMock(side_effect=subprocess.CalledProcessError(returncode=1, cmd=['flake8'], stderr=b"Error details"))
    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("def code(): pass")
        assert result['error'] is True
        assert "Flake8 analysis failed" in result['error_message']
        assert result['static_analysis'] == []

    # Assert that "Error details" is in the captured log output
    log_records = caplog.records
    stderr_logged = False
    for record in log_records:
        if record.levelname == 'ERROR' and "Flake8 stderr: b'Error details'" in record.message:
            stderr_logged = True
            break
    assert stderr_logged, "Expected 'Flake8 stderr: b'Error details'' to be logged"

def test_analyze_python_flake8_filenotfounderror(review_agent):
    """Test handling of FileNotFoundError when flake8 is not found."""
    mock_run = MagicMock(side_effect=FileNotFoundError("flake8 not found"))
    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("def code(): pass")
        assert result['error'] is True
        assert "Flake8 executable not found" in result['error_message']
        assert result['static_analysis'] == []

def test_analyze_python_flake8_generic_exception(review_agent):
    """Test handling of generic exceptions during flake8 execution."""
    mock_run = MagicMock(side_effect=Exception("Generic flake8 error"))
    with patch('subprocess.run', mock_run):
        result = review_agent.analyze_python("def code(): pass")
        assert result['error'] is True
        assert "Error running flake8" in result['error_message']
        assert result['static_analysis'] == []

def test_store_findings_kg_integration_with_severity(review_agent):
    """Test store_findings correctly stores severity data in KG."""
    mock_kg = MagicMock(spec=KnowledgeGraph)
    review_agent.kg = mock_kg

    sample_findings = {
        'static_analysis': [
            {'file': 'test.py', 'line': '1', 'col': '1', 'code': 'E302', 'msg': 'test message', 'severity': 'error'} # Findings now include severity
        ]
    }
    code_hash_str = "1234567890"

    review_agent.store_findings(sample_findings, code_hash_str)

    mock_kg.add_node.assert_called_once()
    added_node = mock_kg.add_node.call_args[0][0]

    assert added_node.type == "code_review"
    assert "Static analysis findings from flake8 with severity" in added_node.content # Updated assertion
    assert isinstance(added_node.metadata['findings'], list)

    finding = added_node.metadata['findings'][0] # Get the first finding
    assert finding['severity'] == 'error' # Check severity in stored finding
    assert 'file' in finding
    assert 'line' in finding
    assert 'col' in finding
    assert 'code' in finding
    assert 'msg' in finding

def test_analyze_python_stores_findings_in_kg(review_agent):
    """Test that analyze_python calls store_findings and stores results in KG."""
    mock_kg = MagicMock(spec=KnowledgeGraph)  # Mock KnowledgeGraph explicitly
    review_agent.kg = mock_kg  # Inject mock KG into agent
    mock_run = MagicMock()
    mock_run.return_value.stdout = "test.py:1:1: E302 expected 2 blank lines, found 1"

    with patch('subprocess.run', mock_run):
        code_sample = "def example(): pass"
        code_hash_str = str(hash(code_sample)) # Calculate expected code hash
        review_agent.analyze_python(code_sample)

    mock_kg.add_node.assert_called_once()  # Verify add_node was called

    call_args = mock_kg.add_node.call_args
    node_arg = call_args[0][0]  # Get the Node argument passed to add_node

    assert isinstance(node_arg, Node)
    assert node_arg.type == 'code_review'
    assert node_arg.content == 'Static analysis findings from flake8 with severity' # Updated content check
    assert node_arg.metadata['code_hash'] == code_hash_str
    assert len(node_arg.metadata['findings']) == 1 # Check findings are stored
    assert 'timestamp' in node_arg.metadata
