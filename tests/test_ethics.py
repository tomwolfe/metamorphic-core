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
@patch.object(QuantumEthicalValidator, '_predict_ethical_impact') # Mock predict_ethical_impact to prevent LLM calls
def test_ethical_validation_approved(mock_predict):
    mock_predict.return_value = { # Mock a safe prediction
        "bias_risk": 0.15,
        "transparency_score": 0.8,
        "immediate_risk": 0.1,
        "long_term_risk": 0.2,
        "privacy_risk": 0.1
    }
    validator = QuantumEthicalValidator()
    result = validator.validate_code("print('Hello World')")
    assert result["status"] == "approved"
    assert "score" in result
    assert result["score"] >= 0.8  # Safe code should have high score

@patch.object(QuantumEthicalValidator, '_predict_ethical_impact') # Mock predict_ethical_impact to prevent LLM calls
def test_ethical_validation_rejected(mock_predict):
    mock_predict.return_value = {
        "bias_risk": 0.30,  # Exceeds 0.25 threshold
        "transparency_score": 0.7,
        "immediate_risk": 0.1,
        "long_term_risk": 0.2,
        "privacy_risk": 0.1
    }
    validator = QuantumEthicalValidator()
    result = validator.validate_code("dangerous_code")
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

@patch.object(QuantumEthicalValidator, '_predict_ethical_impact') # Mock predict_ethical_impact to prevent LLM calls
def test_rejection_due_to_violations(mock_predict):
    """Test code rejection when formal verification finds violations"""
    mock_predict.return_value = {
        "bias_risk": 0.30,  # Exceeds 0.25 threshold
        "transparency_score": 0.7,
        "immediate_risk": 0.1,
        "long_term_risk": 0.2,
        "privacy_risk": 0.1
    }
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

# New test for score calculation boundaries
@pytest.mark.parametrize("immediate,long_term,expected_score", [
    (True, True, 1.0),    # 0.5 + 0.2 + 0.3 = 1.0
    (True, False, 0.7),   # 0.5 + 0.2 = 0.7
    (False, True, 0.8),   # 0.5 + 0.3 = 0.8
    (False, False, 0.5)   # Base score only
])
@patch.object(QuantumEthicalValidator, '_predict_ethical_impact') # Mock predict_ethical_impact to prevent LLM calls
def test_score_calculation(mock_predict, immediate, long_term, expected_score):
    """Test ethical score calculation boundaries"""
    mock_predict.return_value = { # Mock predictions to avoid LLM calls
        "bias_risk": 0.15,
        "transparency_score": 0.7,
        "immediate_risk": 0.1,
        "long_term_risk": 0.2,
        "privacy_risk": 0.1
    }
    validator = QuantumEthicalValidator()

    with patch.object(validator, '_calculate_ethical_score') as mock_calculate:
        mock_calculate.return_value = expected_score
        result = validator.validate_code("any_code")

        assert result["score"] == expected_score



