from z3 import *
from datetime import datetime
import json
from typing import Dict, List
from .z3_serializer import Z3JSONEncoder

class FormalSpecification:
    def __init__(self):
        self.solver = Solver()
        self.solver.set(unsat_core=True)  # Add this line
        self.constraints = {}
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

    def add_safety_invariant(self, constraint: str):
        """Register safety constraint with automatic variable binding"""
        try:
            z3_expr = self._parse_constraint(constraint)
            self.constraints[constraint] = z3_expr
            self.proofs.append({
                'type': 'invariant',
                'constraint': constraint,
                'z3_expression': str(z3_expr),
                'timestamp': datetime.utcnow().isoformat()
            })
        except Exception as e:
            raise ValueError(f"Constraint parsing failed: {str(e)}")

    def add_ethical_guardrail(self, constraint: str):
        """Register ethical constraint with automatic binding"""
        try:
            z3_expr = self._parse_constraint(constraint)
            self.constraints[constraint] = z3_expr
            self.proofs.append({
                'type': 'guardrail',
                'constraint': constraint,
                'z3_expression': str(z3_expr),
                'timestamp': datetime.utcnow().isoformat()
            })
        except Exception as e:
            raise ValueError(f"Guardrail parsing failed: {str(e)}")

    def verify_predictions(self, predictions: Dict[str, float]) -> Dict:
        """Verify predictions against all registered constraints"""
        results = {
            "verified": True,
            "violations": [],
            "proofs": []
        }

        self.solver.push()
        try:
            # Add all constraints
            for constr in self.constraints.values():
                self.solver.add(constr)

            # Add prediction equalities
            canonical_map = {
                "bias_risk": "BiasRisk",
                "transparency_score": "TransparencyScore",
                "immediate_risk": "ImmediateRisk",
                "long_term_risk": "LongTermRisk",
                "privacy_risk": "PrivacyRisk"
            }
            
            for pred_key, pred_value in predictions.items():
                z3_var = canonical_map.get(pred_key)
                if z3_var and z3_var in self.z3_vars:
                    self.solver.add(self.z3_vars[z3_var] == pred_value)

            check_result = self.solver.check()

            if check_result == sat:
                results["verified"] = True
                self.valid_constraints = set(self.constraints.keys())
            elif check_result == unsat:
                results["verified"] = False
                results["violations"] = self._get_unsat_core()
                self.valid_constraints -= set(results["violations"])
                self.last_violations = results["violations"]
            else:
                results["verified"] = "unknown"

        finally:
            self.solver.pop()

        results["proofs"] = self.proofs
        return results

    def _parse_constraint(self, constraint: str):
        """Convert natural language constraint to Z3 expression"""
        if "never exceeds" in constraint:
            parts = constraint.split("never exceeds")
            # Normalize variable name by removing spaces
            var_name = parts[0].strip().replace(" ", "")
            value = float(parts[1].strip())
            return self.z3_vars[var_name] <= value
        elif "never drops below" in constraint:
            parts = constraint.split("never drops below")
            var_name = parts[0].strip().replace(" ", "")
            value = float(parts[1].strip())
            return self.z3_vars[var_name] >= value
        else:
            raise ValueError(f"Unsupported constraint format: {constraint}")
            
    def _get_unsat_core(self) -> List[str]:
        """Identify violated constraints from unsat core"""
        core = self.solver.unsat_core()
        return [self._z3_expr_to_constraint_name(expr) for expr in core]

    def _z3_expr_to_constraint_name(self, expr) -> str:
        """Map Z3 expression back to original constraint string"""
        for name, z3_expr in self.constraints.items():
            if z3_expr == expr:
                return name
        return str(expr)

    def get_constraint_names(self) -> List[str]:
        """Get list of registered constraints"""
        return list(self.constraints.keys())

    def get_valid_constraints(self) -> List[str]:
        """Get list of currently satisfied constraints"""
        return list(self.valid_constraints)

    def get_violated_constraints(self) -> List[str]:
        """Get list of violated constraints from last verification"""
        return self.last_violations
