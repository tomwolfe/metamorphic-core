# tests/test_ethics.py
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import pytest
import json
from unittest.mock import patch, MagicMock
from datetime import datetime
from src.core.ethics.governance import QuantumEthicalValidator
from src.core.quantum.ethical_validation import EthicalQuantumCore

# Original tests
def test_ethical_validation_approved():
    validator = QuantumEthicalValidator()
    with patch.object(validator.security_agent, 'run_zap_baseline_scan') as mock_scan:
        mock_scan.return_value = {'alerts': [], 'high_risk': 0}
        result = validator.validate_code("print('Hello World')")
        assert result["status"] == "approved"
        assert "score" in result
        assert result["score"] >= 0.7  # Safe code should have high score

def test_ethical_validation_rejected():
    validator = QuantumEthicalValidator()
    result = validator.validate_code("import os; os.system('rm -rf /')")
    assert result["status"] == "rejected"
    assert result["score"] < 0.7

def test_audit_logging():
    validator = QuantumEthicalValidator()
    result = validator.validate_code("print('Test')")
    assert "timestamp" in result
    assert "code_sample_hash" in result

# Enhanced tests
@pytest.fixture
def mock_verifier():
    mock = MagicMock()
    mock.verify_predictions.return_value = {
        "verified": True,
        "violations": [],
        "proofs": []
    }
    return mock

# File: tests/test_ethics.py

def test_approval_with_valid_proof(mock_verifier):
    """Test code approval when formal proofs verify all constraints"""
    with patch('src.core.ethics.governance.FormalSpecification') as mock_spec:
        mock_spec_instance = mock_spec.return_value
        mock_spec_instance.verify_predictions.return_value = {
            "verified": True,
            "violations": []
        }
        validator = QuantumEthicalValidator()
        result = validator.validate_code("ethical_code = 42")

    assert result["status"] == "approved"
    assert result["score"] >= 0.7

def test_rejection_due_to_violations():
    """Test code rejection when formal verification finds violations"""
    validator = QuantumEthicalValidator()

    # Force verification failure
    with patch.object(validator.security_agent, 'run_zap_baseline_scan') as mock_security_scan:
        mock_security_scan.return_value = {"alerts": [{"riskcode": '3'}], "scan_id": 'test_scan'} # Mock high-risk alert

        result = validator.validate_code("risky_code = 666")

    assert result["status"] == "rejected"
    assert result["score"] < 0.7

def test_error_handling_in_validation():
    """Test graceful handling of validation errors"""
    validator = QuantumEthicalValidator()

    with patch.object(validator.spec_analyzer, 'analyze_python_spec') as mock_spec_analysis:
        mock_spec_analysis.side_effect = Exception("Spec analysis failed")

        result = validator.validate_code("buggy_code = True")

    assert result["status"] == "error"
    assert "error" in result
    assert result["score"] == 0.0

# New test for score calculation boundaries
@pytest.mark.parametrize("immediate,long_term,expected_score", [
    (True, True, 1.0),    # 0.5 + 0.2 + 0.3 = 1.0
    (True, False, 0.7),   # 0.5 + 0.2 = 0.7
    (False, True, 0.8),   # 0.5 + 0.3 = 0.8
    (False, False, 0.5)   # Base score only
])
def test_score_calculation(immediate, long_term, expected_score):
    """Test ethical score calculation boundaries"""
    validator = QuantumEthicalValidator()

    with patch.object(validator, '_calculate_score') as mock_calculate: # Corrected patch target
        mock_calculate.return_value = expected_score
        result = validator.validate_code("any_code")

    assert result["score"] == expected_score
