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
    result = validator.validate_code("print('Hello World')")
    assert result["status"] == "approved"
    assert result["score"] >= 0.7

def test_ethical_validation_rejected():
    validator = QuantumEthicalValidator()
    result = validator.validate_code("Sensitive code with high risk")
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
    with patch.object(validator.formal_verifier, 'verify_predictions') as mock_verify:
        mock_verify.return_value = {
            "verified": False,
            "violations": ["BiasRisk > 0.25"],
            "proofs": []
        }
        
        result = validator.validate_code("risky_code = 666")
        
    assert result["status"] == "rejected"
    assert result["score"] < 0.7

def test_error_handling_in_validation():
    """Test graceful handling of validation errors"""
    validator = QuantumEthicalValidator()
    
    with patch.object(validator.formal_verifier, 'verify_predictions') as mock_verify:
        mock_verify.side_effect = Exception("Verification failed")
        
        result = validator.validate_code("buggy_code = True")
        
    assert result["status"] == "error"
    assert "error" in result
    assert result["score"] == 0.0

@pytest.mark.parametrize("verified,expected_score", [
    (True, 1.0),
    (False, 0.5)
])
def test_score_calculation(verified, expected_score):
    validator = QuantumEthicalValidator()
    with patch.object(validator.formal_verifier, 'verify_predictions') as mock_verify:
        mock_verify.return_value = {"verified": verified}
        result = validator.validate_code("any_code")
        assert result["score"] == expected_score
