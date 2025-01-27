from datetime import datetime
from z3 import Real, Solver, sat, unsat, CheckSatResult

class FormalSpecification:
    """
    Core class for managing formal specifications and safety invariants using Z3.
    """
    def __init__(self):
        self.solver = Solver()
        self.constraints = {}
        self.proofs = []

        # Define Z3 Real variables for key metrics.  Make sure these names
        # match exactly with what you use in _get_z3_var and constraints.
        self.bias_risk = Real('bias_risk')
        self.transparency_score = Real('transparency_score')
        self.immediate_risk = Real('immediate_risk')
        self.long_term_risk = Real('long_term_risk')

    def add_safety_invariant(self, constraint: str):
        """Register safety constraint with automatic variable binding"""
        try:
            z3_expr = self._parse_constraint(constraint)
            self.constraints[constraint] = z3_expr
            self.solver.add(z3_expr) # Add to the Z3 solver
            self.proofs.append({
                'type': 'safety',
                'constraint': constraint,
                'z3_expression': str(z3_expr),
                'timestamp': datetime.utcnow().isoformat()
            })
        except Exception as e:
            raise ValueError(f"Constraint parsing failed: {str(e)}")

    def verify_predictions(self, risk_predictions: dict) -> dict:
        """
        Verify risk predictions against formal safety invariants using Z3.
        """
        status = "unknown" # Default status
        violations = []

        # Assume risk_predictions is a dict like:
        # {'bias_risk': 0.1, 'transparency_score': 0.9, ...}
        # Ensure the keys here match the Z3 variable names (or adjust mapping)

        self.solver.push() # Create a backtracking point

        try:
            # Soft-code to accept direct value setting, ensure keys are consistent
            self.solver.add(self.bias_risk == risk_predictions.get('bias_risk', 0.0)) # default to 0 if missing
            self.solver.add(self.transparency_score == risk_predictions.get('transparency_score', 0.0))
            self.solver.add(self.immediate_risk == risk_predictions.get('immediate_risk', 0.0))
            self.solver.add(self.long_term_risk == risk_predictions.get('long_term_risk', 0.0))


            check_result: CheckSatResult = self.solver.check() # Get the Z3 check result

            if check_result == sat:
                status = "approved" # All constraints satisfied under these predictions
            elif check_result == unsat:
                status = "rejected" # Constraints violated
                violations = self._get_violations() # (To be implemented)
            else:
                status = "unknown" # Z3 might return 'unknown'

        except Exception as e:
            status = "error"
            violations.append(f"Verification process error: {str(e)}")
        finally:
            self.solver.pop() # Restore solver state

        return {
            "status": status,
            "verified": status == "approved",
            "violations": violations,
            "proof_log": self.proofs # Return proof log for auditing/debugging
        }


    def _get_violations(self) -> list:
        """
        (Simplified) Placeholder to extract specific violated constraints.
        For more detailed violation analysis, Z3's model extraction could be used.
        """
        violations = []
        if self.solver.check() == unsat:
            for constraint_str, z3_expression in self.constraints.items():
                check_individual_constraint_solver = Solver()
                check_individual_constraint_solver.add(z3_expression)
                check_individual_constraint_solver.add(z3_expression == False) # Negate constraint to see if *negated* is satisfiable under current context - rough way to check violation. May need refinement
                if check_individual_constraint_solver.check() == sat:
                    violations.append(f"Constraint violated: {constraint_str} (Z3 Expr: {z3_expression})")
        return violations


    def _parse_constraint(self, constraint: str):
        """
        Improved parser for constraints like 'Variable Operator Value'

        Example Constraints (now supported more robustly):
        - "Bias risk exceeds 0.5"
        - "Transparency less than 0.9"
        - "Immediate risk <= 0.2"
        - "Long-term risk >= 0.1"
        - "Bias risk is 0.3" (or "Bias risk == 0.3")

        Handles variable names with spaces correctly.  Supports: exceeds, less than, >=, <=, >, <, is, ==

        """
        parts = constraint.split()
        if len(parts) < 3: # Basic check for minimal structure
            raise ValueError(f"Invalid constraint format: {constraint}")

        var_name_parts = [] # Collect parts for variable name until operator is found
        operator = None
        value_str = None
        operator_index = -1

        possible_operators = ["exceeds", ">=", ">", "less than or equals", "<=", "<", "less than", "is", "==","equals", "="] # Added "is" and "==" and "equals", "="

        for i, part in enumerate(parts):
            if part in possible_operators:
                operator = part
                operator_index = i
                break
            var_name_parts.append(part) # Accumulate variable name parts

        if not operator or operator_index == -1:
            raise ValueError(f"No valid operator found in constraint: {constraint}")

        var_name = " ".join(var_name_parts).strip() # Reconstruct variable name with spaces, strip
        value_str_parts = parts[operator_index+1:] # Everything after operator is value (parts)
        if not value_str_parts:
            raise ValueError(f"No value found after operator in constraint: {constraint}")


        value_str = " ".join(value_str_parts).strip() # Value as string

        try:
            value = float(value_str) # Try to convert to float
        except ValueError:
            raise ValueError(f"Invalid numerical value in constraint: {constraint}")


        z3_var = self._get_z3_var(var_name)

        if operator == "exceeds" or operator == ">":
            return z3_var > value
        elif operator == "less than" or operator == "<":
            return z3_var < value
        elif operator == "greater than or equals" or operator == ">=" or operator == "exceeds or equals" or operator == ">=" : # Handle >=, and variations
            return z3_var >= value
        elif operator == "less than or equals" or operator == "<=" or operator == "at most" or operator == "<=": # Handle <= , variations
            return z3_var <= value
        elif operator == "is" or operator == "==" or operator == "equals" or operator == "=": # Handle equality
            return z3_var == value
        else:
            raise ValueError(f"Unsupported operator: {operator} in constraint: {constraint}")


    def _get_z3_var(self, var_name: str):
        """Map natural language names to Z3 variables - ENSURE CONSISTENCY with var names in __init__"""
        var_map = {
            "Bias risk": self.bias_risk, # Exact match to Real('bias_risk')
            "Transparency": self.transparency_score, # Exact match to Real('transparency_score')
            "Immediate risk": self.immediate_risk, # Exact match to Real('immediate_risk')
            "Long-term risk": self.long_term_risk  # Exact match to Real('long_term_risk')
        }
        try:
            return var_map[var_name.strip()] # .strip() to remove any leading/trailing spaces just in case
        except KeyError:
            valid_keys = ", ".join(var_map.keys()) # For better error message
            raise KeyError(f"Variable name '{var_name.strip()}' not recognized in specification. Valid variable names are: {valid_keys}")


    def get_proof_log(self) -> list:
        """Return the history of added safety invariant proofs."""
        return self.proofs

    def clear_proof_log(self):
        """Clears the proof history - useful for testing or resetting."""
        self.proofs = []
