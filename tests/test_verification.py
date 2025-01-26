# test_verification.py
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import sys
import json
import os

# Add project root to Python path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from src.core.verification.specification import FormalSpecification
from src.core.verification.z3_serializer import Z3JSONEncoder

def main():
    try:
        # Initialize formal specification system
        spec = FormalSpecification()
        
        # Add constraints from original ethical framework
        print("\n=== Registering Constraints ===")
        spec.add_safety_invariant("Bias risk never exceeds 0.25")
        spec.add_ethical_guardrail("Transparency never drops below 0.4")
        spec.add_safety_invariant("Immediate risk never exceeds 0.2")
        
        # Test case 1: Valid prediction
        print("\n=== Testing Valid Prediction ===")
        good_prediction = {
            "bias_risk": 0.18,
            "transparency_score": 0.6,
            "immediate_risk": 0.15
        }
        result = spec.verify_predictions(good_prediction)
        print(json.dumps(result, indent=2, cls=Z3JSONEncoder))

        # Test case 2: Invalid prediction
        print("\n=== Testing Invalid Prediction ===")
        bad_prediction = {
            "bias_risk": 0.3,
            "transparency_score": 0.3,
            "immediate_risk": 0.25
        }
        result = spec.verify_predictions(bad_prediction)
        print(json.dumps(result, indent=2, cls=Z3JSONEncoder))
        
    except Exception as e:
        print(f"\n!!! Test failed: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()
