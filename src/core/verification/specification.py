from z3 import *
from datetime import datetime
import json
from typing import Dict, List
from .z3_serializer import Z3JSONEncoder

class FormalSpecification:
    def __init__(self):
        self.solver = Solver()
        self.solver.set(unsat_core=True)
        self.constraints = {}
        self.parsed_constraints = []  # Track parsed constraint details
        self.proofs = []
        self.last_violations = []
        self.valid_constraints = set()
        self._init_z3_vars()

    def _init_z3_vars(self):
        """Initialize all Z3 variables used in constraints"""
        self.z3_vars = {
            'BiasRisk': Real('BiasRisk'),
            'TransparencyScore': Real('TransparencyScore'),
            'ImmediateRisk': Real('ImmediateRisk'),
            'LongTermRisk': Real('LongTermRisk'),
            'PrivacyRisk': Real('PrivacyRisk')
        }

    def _parse_constraint(self, constraint: str) -> dict:
        """Parse natural language constraint into structured format"""
        if "never exceeds" in constraint:
            parts = constraint.split("never exceeds")
            var_name = parts[0].strip().replace(" ", "")
            value = float(parts[1].strip())
            return {
                'z3_expr': self.z3_vars[var_name] <= value,
                'variable': var_name,
                'operator': '<=',
                'threshold': value
            }
        elif "never drops below" in constraint:
            parts = constraint.split("never drops below")
            var_name = parts[0].strip().replace(" ", "")
            value = float(parts[1].strip())
            return {
                'z3_expr': self.z3_vars[var_name] >= value,
                'variable': var_name,
                'operator': '>=',
                'threshold': value
            }
        else:
            raise ValueError(f"Unsupported constraint format: {constraint}")

    def _add_constraint(self, constraint: str, constraint_type: str):
        """Internal method to add constraints with structured parsing"""
        try:
            parsed = self._parse_constraint(constraint)
            self.constraints[constraint] = parsed['z3_expr']
            self.parsed_constraints.append({
                'name': constraint,
                'variable': parsed['variable'],
                'operator': parsed['operator'],
                'threshold': parsed['threshold']
            })
            self.proofs.append({
                'type': constraint_type,
                'constraint': constraint,
                'z3_expression': str(parsed['z3_expr']),
                'timestamp': datetime.utcnow().isoformat()
            })
        except Exception as e:
            raise ValueError(f"{constraint_type} parsing failed: {str(e)}")

    def add_safety_invariant(self, constraint: str):
        """Register safety constraint with automatic variable binding"""
        self._add_constraint(constraint, 'invariant')

    def add_ethical_guardrail(self, constraint: str):
        """Register ethical constraint with automatic binding"""
        self._add_constraint(constraint, 'guardrail')

    def get_constraint_names(self) -> List[str]:
        """Get list of registered constraints"""
        return list(self.constraints.keys())

    def get_valid_constraints(self) -> set: # Changed return type to set to match previous fix and current usage
        """Get set of currently satisfied constraints""" # Corrected docstring to reflect set return
        return self.valid_constraints

    def get_violated_constraints(self) -> List[str]:
        """Get list of violated constraints from last verification"""
        return self.last_violations

    def verify_predictions(self, predictions: Dict[str, float]) -> Dict:
        """Verify predictions against all registered constraints"""
        results = {
            "verified": True,
            "violations": [],
            "proofs": []
        }

        self.solver.push()
        try:
            # Add all constraints to solver
            for constraint_str, constr in self.constraints.items():
                self.solver.assert_and_track(constr, constraint_str)

            # Map predictions to Z3 variables
            canonical_map = {
                "bias_risk": "BiasRisk",
                "transparency_score": "TransparencyScore",
                "immediate_risk": "ImmediateRisk",
                "long_term_risk": "LongTermRisk",
                "privacy_risk": "PrivacyRisk"
            }

            # Add prediction equalities to solver
            for pred_key, pred_value in predictions.items():
                z3_var = canonical_map.get(pred_key)
                if z3_var and z3_var in self.z3_vars:
                    self.solver.add(self.z3_vars[z3_var] == pred_value)

            check_result = self.solver.check()

            if check_result == sat:
                results["verified"] = True
                self.valid_constraints = set(self.constraints.keys())
            elif check_result == unsat:
                # Check all constraints against predictions directly
                violations = []
                pred_values = {canonical_map[k]: v
                             for k, v in predictions.items()
                             if k in canonical_map}

                for pc in self.parsed_constraints:
                    current_value = pred_values.get(pc['variable'])
                    if current_value is None:
                        continue
                    if (pc['operator'] == '<=' and current_value > pc['threshold']) or \
                       (pc['operator'] == '>=' and current_value < pc['threshold']):
                        violations.append(pc['name'])

                results["verified"] = False
                results["violations"] = violations
                self.valid_constraints = set(self.constraints.keys()) - set(violations)
                self.last_violations = violations
            else:
                results["verified"] = "unknown"

        finally:
            self.solver.pop()

        results["proofs"] = self.proofs
        return results
