# tests/test_ethics.py
import sys
import os
import pytest
import json
from unittest.mock import patch, MagicMock
from datetime import datetime
from jsonschema import ValidationError, SchemaError # Import specific errors
from collections import deque # Import deque

# Ensure the src directory is in the Python path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..')))

from src.core.ethics.governance import QuantumEthicalValidator, EthicalGovernanceEngine

# --- Tests for QuantumEthicalValidator (Keep existing mocks/tests as placeholders) ---

@pytest.mark.skip(reason="QuantumEthicalValidator relies on complex non-MVP components and placeholders.")
@patch.object(QuantumEthicalValidator, '_predict_ethical_impact')
@patch('src.core.agents.test_generator.TestGenAgent.generate_tests')
def test_ethical_validation_approved(mock_generate_tests, mock_predict):
    """Placeholder: Test approval path for QuantumEthicalValidator."""
    mock_predict.return_value = { "bias_risk": 0.1, "transparency_score": 0.9, "immediate_risk": 0.05 } # Example safe values
    mock_generate_tests.return_value = ["placeholder test"]
    validator = QuantumEthicalValidator()
    # Mock dependencies that might be missing or complex
    validator.audit_logger = MagicMock()
    validator.formal_verifier = MagicMock()
    validator.formal_verifier.verify_predictions.return_value = {"verified": True} # Assume verification passes

    result = validator.validate_code("print('Hello World')")
    assert result["status"] == "approved"
    assert "score" in result
    # assert result["score"] >= 0.7 # Adjust score assertion based on actual calculation if needed

@pytest.mark.skip(reason="QuantumEthicalValidator relies on complex non-MVP components and placeholders.")
@patch.object(QuantumEthicalValidator, '_predict_ethical_impact')
@patch('src.core.agents.test_generator.TestGenAgent.generate_tests')
def test_ethical_validation_rejected(mock_generate_tests, mock_predict):
    """Placeholder: Test rejection path for QuantumEthicalValidator."""
    mock_predict.return_value = { "bias_risk": 0.8, "transparency_score": 0.2, "immediate_risk": 0.5 } # Example risky values
    mock_generate_tests.return_value = ["placeholder test"]
    validator = QuantumEthicalValidator()
    validator.audit_logger = MagicMock()
    validator.formal_verifier = MagicMock()
    validator.formal_verifier.verify_predictions.return_value = {"verified": False} # Assume verification fails

    result = validator.validate_code("import os; os.system('dangerous')")
    assert result["status"] == "rejected"
    # assert result["score"] < 0.7

# --- Tests for EthicalGovernanceEngine (Week 4 Focus) ---

@pytest.fixture(scope="module")
def engine():
    """Fixture to create an EthicalGovernanceEngine instance once per module."""
    return EthicalGovernanceEngine()

@pytest.fixture(scope="module")
def schema(engine):
    """Fixture to load the schema once per module."""
    return engine._load_schema() # Use the internal method to get the loaded schema

# --- Policy Loading Tests ---

def test_load_policy_valid(engine, valid_policy_path):
    """Test loading a valid policy file that conforms to the schema."""
    policy = engine.load_policy_from_json(valid_policy_path)
    assert isinstance(policy, dict)
    assert policy["policy_name"] == "Strict Bias Risk Policy"
    assert "constraints" in policy

def test_load_policy_file_not_found(engine):
    """Test loading a non-existent policy file."""
    with pytest.raises(FileNotFoundError):
        engine.load_policy_from_json("non_existent_policy.json")

def test_load_policy_invalid_json(engine, tmp_path):
    """Test loading a file with invalid JSON content."""
    invalid_json_file = tmp_path / "invalid.json"
    invalid_json_file.write_text("{ 'malformed': json, }")
    with pytest.raises(json.JSONDecodeError):
        engine.load_policy_from_json(str(invalid_json_file))

def test_load_policy_schema_violation_missing_required(engine, tmp_path, schema):
    """Test loading a policy missing a required top-level field."""
    policy_file = tmp_path / "missing_req.json"
    policy_data = {
      # "policy_name": "Missing Name", # Required field missing
      "description": "Policy missing required name",
      "constraints": {
        "BiasRisk": {"threshold": 0.1, "enforcement_level": 3},
        "TransparencyScore": {"threshold": 0.5, "enforcement_level": 2},
        "SafetyBoundary": {"threshold": 0.8, "enforcement_level": 2}
      }
    }
    policy_file.write_text(json.dumps(policy_data))
    with pytest.raises(ValidationError) as excinfo:
        engine.load_policy_from_json(str(policy_file))
    assert "'policy_name' is a required property" in str(excinfo.value)

def test_load_policy_schema_violation_wrong_type(engine, tmp_path, schema):
    """Test loading a policy with a field of the wrong type."""
    policy_file = tmp_path / "wrong_type.json"
    policy_data = {
      "policy_name": "Wrong Type Policy",
      "description": "Threshold is wrong type",
      "constraints": {
        "BiasRisk": {"threshold": "should_be_number", "enforcement_level": 3}, # Wrong type
        "TransparencyScore": {"threshold": 0.5, "enforcement_level": 2},
        "SafetyBoundary": {"threshold": 0.8, "enforcement_level": 2}
      }
    }
    policy_file.write_text(json.dumps(policy_data))
    with pytest.raises(ValidationError) as excinfo:
        engine.load_policy_from_json(str(policy_file))
    # Assert message content which includes path info
    assert "'should_be_number' is not of type 'number'" in str(excinfo.value)
    assert "(path: constraints/BiasRisk/threshold)" in str(excinfo.value)
    # Removed assertion checking excinfo.value.path directly as it's empty


def test_load_policy_schema_violation_missing_constraint_field(engine, tmp_path, schema):
    """Test loading a policy missing a required field within a constraint."""
    policy_file = tmp_path / "missing_constraint_field.json"
    policy_data = {
      "policy_name": "Missing Field Policy",
      "description": "BiasRisk missing threshold",
      "constraints": {
        "BiasRisk": {#"threshold": 0.1, # Missing
                      "enforcement_level": 3},
        "TransparencyScore": {"threshold": 0.5, "enforcement_level": 2},
        "SafetyBoundary": {"threshold": 0.8, "enforcement_level": 2}
      }
    }
    policy_file.write_text(json.dumps(policy_data))
    with pytest.raises(ValidationError) as excinfo:
        engine.load_policy_from_json(str(policy_file))
    # Assert message content which includes path info
    assert "'threshold' is a required property" in str(excinfo.value)
    assert "(path: constraints/BiasRisk)" in str(excinfo.value)
    # Removed assertion checking excinfo.value.path directly as it's empty

# --- Policy Enforcement Tests ---

# Policy Fixtures (using paths relative to tests directory)
@pytest.fixture(scope="module")
def strict_policy(engine, valid_policy_path):
    return engine.load_policy_from_json(valid_policy_path)

@pytest.fixture(scope="module")
def moderate_policy(engine, policy_safety_moderate_path):
     # Assuming 'policy_safety_moderate.json' exists at this relative path
    return engine.load_policy_from_json(policy_safety_moderate_path)

@pytest.fixture(scope="module")
def minimum_transparency_policy(engine, policy_transparency_minimum_path):
     # Assuming 'policy_transparency_minimum.json' exists at this relative path
    return engine.load_policy_from_json(policy_transparency_minimum_path)

# Path fixtures (adjust if your test structure is different)
@pytest.fixture(scope="module")
def valid_policy_path():
    # Correct relative path - go up one level from tests/
    return os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'policies', 'policy_bias_risk_strict.json'))

@pytest.fixture(scope="module")
def policy_safety_moderate_path():
    # Correct relative path
    return os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'policies', 'policy_safety_moderate.json'))

@pytest.fixture(scope="module")
def policy_transparency_minimum_path():
    # Correct relative path
    return os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'policies', 'policy_transparency_minimum.json'))


# Code Snippet Fixtures
@pytest.fixture
def compliant_code():
    # Removed potentially triggering keyword "offensive" from comment
    return '''"""Module docstring"""
def example():
    """Function docstring"""
    # Non-triggering, safe code
    x = 1 + 1
    return x
'''

@pytest.fixture
def bias_violation_code(strict_policy):
    # Get a keyword from the strict policy to ensure violation
    keyword = strict_policy["constraints"]["BiasRisk"]["keywords"][0]
    return f"def bad_function():\n    print('This code contains {keyword}')"

@pytest.fixture
def transparency_violation_code():
    return "def undocumented_function():\n    pass" # No docstring

@pytest.fixture
def safety_violation_code(strict_policy):
    # Get an unsafe op from the strict policy
    unsafe_op = strict_policy["constraints"]["SafetyBoundary"]["unsafe_operations"][0]
    return f"import os\ndef dangerous_function():\n    {unsafe_op}('ls')"

@pytest.fixture
def multiple_violation_code(strict_policy):
     keyword = strict_policy["constraints"]["BiasRisk"]["keywords"][0]
     unsafe_op = strict_policy["constraints"]["SafetyBoundary"]["unsafe_operations"][0]
     return f"import os\ndef very_bad_function():\n    # No docstring\n    print('Triggering: {keyword}')\n    {unsafe_op}('rm -rf /')" # Modified bias trigger slightly


# Enforcement Test Cases
def test_enforce_strict_policy_compliant(engine, strict_policy, compliant_code):
    result = engine.enforce_policy(compliant_code, strict_policy)
    # Assertion updated based on corrected compliant_code fixture
    assert result["overall_status"] == "approved"
    assert result["BiasRisk"]["status"] == "compliant"
    assert result["TransparencyScore"]["status"] == "compliant"
    assert result["SafetyBoundary"]["status"] == "compliant"

def test_enforce_strict_policy_bias_violation(engine, strict_policy, bias_violation_code):
    result = engine.enforce_policy(bias_violation_code, strict_policy)
    assert result["overall_status"] == "rejected"
    assert result["BiasRisk"]["status"] == "violation"
    assert result["TransparencyScore"]["status"] == "violation" # No docstring
    assert result["SafetyBoundary"]["status"] == "compliant"

def test_enforce_strict_policy_transparency_violation(engine, strict_policy, transparency_violation_code):
    result = engine.enforce_policy(transparency_violation_code, strict_policy)
    assert result["overall_status"] == "rejected"
    assert result["BiasRisk"]["status"] == "compliant"
    assert result["TransparencyScore"]["status"] == "violation"
    assert result["SafetyBoundary"]["status"] == "compliant"

def test_enforce_strict_policy_safety_violation(engine, strict_policy, safety_violation_code):
    result = engine.enforce_policy(safety_violation_code, strict_policy)
    assert result["overall_status"] == "rejected"
    assert result["BiasRisk"]["status"] == "compliant"
    assert result["TransparencyScore"]["status"] == "violation" # No docstring
    assert result["SafetyBoundary"]["status"] == "violation"

def test_enforce_strict_policy_multiple_violations(engine, strict_policy, multiple_violation_code):
    result = engine.enforce_policy(multiple_violation_code, strict_policy)
    assert result["overall_status"] == "rejected"
    assert result["BiasRisk"]["status"] == "violation"
    assert result["TransparencyScore"]["status"] == "violation"
    assert result["SafetyBoundary"]["status"] == "violation"

def test_enforce_moderate_policy_safety_compliant(engine, moderate_policy, safety_violation_code):
    # safety_violation_code uses os.system which IS unsafe in moderate policy
    result = engine.enforce_policy(safety_violation_code, moderate_policy)
    assert result["overall_status"] == "rejected" # Still rejected due to safety
    assert result["SafetyBoundary"]["status"] == "violation"

def test_enforce_minimum_transparency_policy_compliant(engine, minimum_transparency_policy, transparency_violation_code):
    # This policy might have a lower threshold, but our check is just presence
    # For MVP, the simple presence check means this still fails.
    result = engine.enforce_policy(transparency_violation_code, minimum_transparency_policy)
    assert result["overall_status"] == "rejected" # Rejected due to transparency
    assert result["TransparencyScore"]["status"] == "violation"

def test_enforce_policy_empty_code(engine, strict_policy):
    """Test enforcing policy on empty code string."""
    result = engine.enforce_policy("", strict_policy)
    # Empty code shouldn't trigger bias or safety, but will fail transparency
    assert result["overall_status"] == "rejected"
    assert result["BiasRisk"]["status"] == "compliant"
    assert result["TransparencyScore"]["status"] == "violation"
    assert result["SafetyBoundary"]["status"] == "compliant"

# FIX: Use the compliant_code fixture for the input code
def test_enforce_policy_missing_constraint_section(engine, tmp_path, compliant_code):
    """Test enforcing a policy where a constraint section is missing in the JSON."""
    policy_file = tmp_path / "missing_constraint.json"
    policy_data = {
      "policy_name": "Missing Constraint Policy",
      "description": "SafetyBoundary constraint is missing",
      "constraints": {
        # SafetyBoundary is missing - THIS IS NOW VALID ACCORDING TO SCHEMA FIX
        "BiasRisk": {"threshold": 0.1, "enforcement_level": 3, "keywords": ["test"]},
        "TransparencyScore": {"threshold": 0.5, "enforcement_level": 2}
      }
    }
    policy_file.write_text(json.dumps(policy_data))
    # Load the policy (should succeed now)
    policy = engine.load_policy_from_json(str(policy_file))

    # Enforce it using the compliant_code fixture
    result = engine.enforce_policy(compliant_code, policy) # Use compliant_code here

    assert "SafetyBoundary" in result # Check the key exists
    # Since the section was missing, the .get() in enforce_policy should use defaults
    assert result["SafetyBoundary"]["status"] == "compliant"
    assert result["SafetyBoundary"]["threshold"] is None # Default threshold from .get() is None if not provided
    assert result["SafetyBoundary"]["enforcement_level"] is None # Default level from .get() is None if not provided

    # Check other statuses for debugging (optional but helpful)
    assert result["BiasRisk"]["status"] == "compliant" # compliant_code doesn't have "test"
    assert result["TransparencyScore"]["status"] == "compliant" # compliant_code has docstrings

    # Final assertion should now pass
    assert result["overall_status"] == "approved"

# --- New Tests for Snippet-Aware Transparency Check ---
# Add these test methods to the TestEthicalGovernanceEngine class

    def test_check_transparency_snippet_no_module_docstring_passes_if_no_defs(self, engine):
        """Test snippet without module docstring passes if it has no internal funcs/classes."""
        code_snippet = "my_list = [1, 2, 3]\nprint(my_list)"
        assert engine._check_transparency(code_snippet, is_snippet=True) is True

    def test_check_transparency_snippet_missing_func_docstring_fails(self, engine):
        """Test snippet fails if an internal function misses a docstring."""
        code_snippet = "def foo():\n    pass # Missing docstring"
        assert engine._check_transparency(code_snippet, is_snippet=True) is False

    def test_check_transparency_snippet_with_func_docstring_passes(self, engine):
        """Test snippet passes if an internal function has a docstring."""
        code_snippet = 'def foo():\n    """My docstring."""\n    pass'
        assert engine._check_transparency(code_snippet, is_snippet=True) is True

    def test_check_transparency_snippet_missing_class_docstring_fails(self, engine):
        """Test snippet fails if an internal class misses a docstring."""
        code_snippet = "class MyClass:\n    def method(self):\n        pass" # Class and method missing docstrings
        assert engine._check_transparency(code_snippet, is_snippet=True) is False

    def test_check_transparency_snippet_with_class_and_method_docstrings_passes(self, engine):
        """Test snippet passes if internal class and method have docstrings."""
        code_snippet = 'class MyClass:\n    """My class."""\n    def method(self):\n        """My method."""\n        pass'
        assert engine._check_transparency(code_snippet, is_snippet=True) is True
    
    def test_check_transparency_full_code_missing_module_docstring_fails(self, engine):
        """Test full code (not snippet) fails if module docstring is missing."""
        full_code = "def foo():\n    '''My func docstring.'''\n    pass"
        assert engine._check_transparency(full_code, is_snippet=False) is False

    def test_check_transparency_full_code_with_all_docstrings_passes(self, engine):
        """Test full code (not snippet) passes if all docstrings are present."""
        full_code = '"""Module docstring."""\ndef foo():\n    """My func docstring."""\n    pass'
        assert engine._check_transparency(full_code, is_snippet=False) is True

    def test_check_transparency_empty_code_fails(self, engine):
        """Test empty code fails for both snippet and full code."""
        assert engine._check_transparency("", is_snippet=True) is False
        assert engine._check_transparency("", is_snippet=False) is False
        
    def test_check_transparency_syntax_error_fails(self, engine):
        """Test code with syntax error fails for both snippet and full code."""
        code_with_syntax_error = "def foo(:\n pass"
        assert engine._check_transparency(code_with_syntax_error, is_snippet=True) is False
        assert engine._check_transparency(code_with_syntax_error, is_snippet=False) is False