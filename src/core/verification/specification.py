# src/core/verification/specification.py
from z3 import *
from datetime import datetime
import json
from typing import Dict
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
            
            # Add all registered constraints
            for constr in self.constraints.values():
                self.solver.add(constr)
            
            # Verify each prediction value
            for pred_key, pred_value in predictions.items():
                var_map = {
                    "BiasRisk": self.bias_risk,
                    "TransparencyScore": self.transparency_score,
                    "ImmediateRisk": self.immediate_risk,
                    "LongTermRisk": self.long_term_risk
                }
                
                if pred_key in var_map:
                    self.solver.add(var_map[pred_key] == pred_value)
            
            # Check satisfaction
            check_result = self.solver.check()
            
            if check_result == sat:
                model = self.solver.model()
                results["verified"] = False
                results["violations"] = self._find_violations(model, predictions)
                results["counterexample"] = json.loads(
                    json.dumps(model, cls=Z3JSONEncoder)
                )
            elif check_result == unsat:
                results["verified"] = True
            else:
                results["verified"] = "unknown"
                
        finally:
            self.solver.pop()
            
        results["proofs"] = self.proofs
        return results

    def _parse_constraint(self, constraint: str):
        """Convert natural language constraint to Z3 expression"""
        # Simple parser for demonstration - extend for more complex constraints
        if "never exceeds" in constraint:
            var_name, value = constraint.split(" never exceeds ")
            return self._get_z3_var(var_name) <= float(value)
        elif "never drops below" in constraint:
            var_name, value = constraint.split(" never drops below ")
            return self._get_z3_var(var_name) >= float(value)
        else:
            raise ValueError(f"Unsupported constraint format: {constraint}")

    def _get_z3_var(self, var_name: str):
        """Map natural language names to Z3 variables"""
        var_map = {
            "Bias risk": self.bias_risk,
            "Transparency": self.transparency_score,
            "Immediate risk": self.immediate_risk,
            "Long-term risk": self.long_term_risk
        }
        return var_map[var_name.strip()]

    def _find_violations(self, model: ModelRef, predictions: Dict) -> list:
        """Identify which predictions violate constraints"""
        violations = []
        for name, constr in self.constraints.items():
            try:
                if not model.eval(constr):
                    violations.append({
                        "constraint": name,
                        "predicted_value": predictions.get(
                            self._get_prediction_key(name), None
                        )
                    })
            except Z3Exception:
                continue
        return violations

    def _get_prediction_key(self, constraint: str) -> str:
        """Map constraint to prediction key"""
        mapping = {
            "Bias risk": "bias_risk",
            "Transparency": "transparency_score",
            "Immediate risk": "immediate_risk",
            "Long-term risk": "long_term_risk"
        }
        for k in mapping:
            if k in constraint:
                return mapping[k]
        return "unknown"
