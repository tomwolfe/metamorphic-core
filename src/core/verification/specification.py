# src/core/verification/specification.py
from z3 import *
from datetime import datetime
import json
from typing import Dict, List
from .z3_serializer import Z3JSONEncoder

class FormalSpecification:
    """Mathematical specification language for system constraints"""

    def __init__(self):
        self.solver = Solver()
        self.constraints = {}
        self.proofs = []

        # Define core ethical variables
        self.bias_risk = Real('BiasRisk')
        self.transparency_score = Real('TransparencyScore')
        self.immediate_risk = Real('ImmediateRisk')
        self.long_term_risk = Real('LongTermRisk')

    def add_safety_invariant(self, constraint: str):
        """Register safety constraint with automatic variable binding"""
        try:
            z3_expr = self._parse_constraint(constraint)
            self.constraints[constraint] = z3_expr
            self.proofs.append({
                'type': 'safety',
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
                'type': 'ethics',
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

        try:
            self.solver.push()

            # Normalize prediction keys
            canonical_map = {
                "bias_risk": "BiasRisk",
                "transparency_score": "TransparencyScore",
                "immediate_risk": "ImmediateRisk",
                "long_term_risk": "LongTermRisk"
            }
            normalized_preds = {
                canonical_map.get(k, k): v
                for k, v in predictions.items()
            }

            # Add all registered constraints
            for constr in self.constraints.values():
                self.solver.add(constr)

            # Add prediction equalities
            var_map = {
                "BiasRisk": self.bias_risk,
                "TransparencyScore": self.transparency_score,
                "ImmediateRisk": self.immediate_risk,
                "LongTermRisk": self.long_term_risk
            }

            for pred_key, pred_value in normalized_preds.items():
                if pred_key in var_map:
                    self.solver.add(var_map[pred_key] == pred_value)

            # Check satisfaction with proper logic
            check_result = self.solver.check()

            if check_result == sat:
                results["verified"] = True
            elif check_result == unsat:
                results["verified"] = False
                results["violations"] = self._find_unsat_core(normalized_preds)
            else:
                results["verified"] = "unknown"

        finally:
            self.solver.pop()

        results["proofs"] = self.proofs
        return results

    def _parse_constraint(self, constraint: str):
        """Convert natural language constraint to Z3 expression"""
        if "never exceeds" in constraint:
            keyword = "never exceeds"
            parts = constraint.split(keyword)
            if len(parts) != 2:
                raise ValueError(f"Invalid constraint format: {constraint}")
            var_name = parts[0].strip()
            value = parts[1].strip()
            return self._get_z3_var(var_name) <= float(value)
        elif "never drops below" in constraint:
            keyword = "never drops below"
            parts = constraint.split(keyword)
            if len(parts) != 2:
                raise ValueError(f"Invalid constraint format: {constraint}")
            var_name = parts[0].strip()
            value = parts[1].strip()
            return self._get_z3_var(var_name) >= float(value)

    def _get_z3_var(self, var_name: str):
        """Map natural language names to Z3 variables"""
        var_map = {
            "Bias risk": self.bias_risk,
            "Transparency": self.transparency_score,
            "Immediate risk": self.immediate_risk,
            "Long-term risk": self.long_term_risk
        }
        return var_map[var_name.strip()]

    def _find_unsat_core(self, predictions: Dict) -> List[str]:
        """Identify which specific constraints are violated"""
        unsat_core = []

        for constraint, expr in self.constraints.items():
            temp_solver = Solver()
            temp_solver.add(expr)

            # Add relevant predictions
            for pred_key, pred_value in predictions.items():
                if pred_key == "BiasRisk":
                    temp_solver.add(self.bias_risk == pred_value)
                elif pred_key == "TransparencyScore":
                    temp_solver.add(self.transparency_score == pred_value)
                elif pred_key == "ImmediateRisk":
                    temp_solver.add(self.immediate_risk == pred_value)
                elif pred_key == "LongTermRisk":
                    temp_solver.add(self.long_term_risk == pred_value)

            if temp_solver.check() == unsat:
                unsat_core.append(constraint)

        return unsat_core

    def get_constraint_names(self) -> List[str]:
        """Get list of registered constraints"""
        return list(self.constraints.keys())
