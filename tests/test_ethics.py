# tests/test_ethics.py
import json
from datetime import datetime
from src.core.ethics.governance import QuantumEthicalValidator
from src.core.quantum.ethical_validation import EthicalQuantumCore

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
