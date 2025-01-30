import sys
import os
import json

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from src.core.verification.specification import FormalSpecification
from src.core.verification.z3_serializer import Z3JSONEncoder

def test_constraint_lifecycle():
    """Test constraint validation lifecycle"""
    spec = FormalSpecification()
    
    # Add sample constraints
    spec.add_safety_invariant("BiasRisk never exceeds 0.25")
    spec.add_ethical_guardrail("TransparencyScore never drops below 0.4")
    
    # Initial state - no validated constraints
    assert len(spec.get_valid_constraints()) == 0
    
    # Test valid predictions
    valid_preds = {
        "bias_risk": 0.2,
        "transparency_score": 0.6
    }
    result = spec.verify_predictions(valid_preds)
    assert result["verified"]
    assert len(spec.get_valid_constraints()) == 2
    assert "BiasRisk never exceeds 0.25" in spec.get_valid_constraints()
    
    # Test invalid predictions
    invalid_preds = {
        "bias_risk": 0.3,
        "transparency_score": 0.3
    }
    result = spec.verify_predictions(invalid_preds)
    assert not result["verified"]
    assert len(result["violations"]) == 2
    assert len(spec.get_valid_constraints()) == 0
    
    # Test partial violation
    mixed_preds = {
        "bias_risk": 0.2,
        "transparency_score": 0.3
    }
    result = spec.verify_predictions(mixed_preds)
    assert not result["verified"]
    assert len(result["violations"]) == 1
    assert "TransparencyScore never drops below 0.4" in result["violations"]
    assert len(spec.get_valid_constraints()) == 1

def main():
    try:
        test_constraint_lifecycle()
        print("\nAll constraint validation tests passed!")
    except AssertionError as e:
        print(f"\nTest failed: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()
