from pathlib import Path
from typing import Dict
import json
from ..quantum.state_preservation import QuantumStatePreserver
from .constraints import EthicalConstraint, ConstraintCategory, RiskProfile, EthicalViolation
from ..quantum.circuit_analysis import QuantumCircuitAnalyzer
from hashlib import sha256

class QuantumEthicalValidator:
    """Applies ethical constraints to quantum code analysis results."""

    def __init__(
        self,
        constraints: list[EthicalConstraint] = None,
        risk_profile: RiskProfile = None,
    ):
        if constraints is None:
            constraints = []
        self.constraints = constraints
        self.risk_profile = risk_profile or RiskProfile()
        self.quantum_analyzer = QuantumCircuitAnalyzer()
        self.state_preserver = QuantumStatePreserver()  # New dependency

    def _hash_code(self, code_sample: str) -> str:
        """Creates a SHA-256 hash of the code sample for anonymity."""
        return sha256(code_sample.encode()).hexdigest()

    def validate_code(self, code_sample: str) -> Dict:
        """Modified to include state preservation"""
        # Existing quantum analysis
        quantum_metrics = self.quantum_analyzer.analyze_quantum_state(
            self._hash_code(code_sample)
        )

        # Preserve quantum state
        state_id = self.state_preserver.preserve_state(code_sample)

        # Existing validation logic
        validation_result = self._apply_ethical_rules(quantum_metrics)

        # Add preservation metadata
        validation_result["quantum_state_id"] = state_id
        return validation_result

    def add_constraint(self, constraint: EthicalConstraint):
        """Adds a new ethical constraint to the validator."""
        self.constraints.append(constraint)

    def set_risk_profile(self, risk_profile: RiskProfile):
        """Sets the risk profile for the validator."""
        self.risk_profile = risk_profile

    def _apply_ethical_rules(self, quantum_metrics: dict) -> dict:
        """
        Applies ethical constraints based on quantum analysis results.
        Args:
            quantum_metrics (dict): A dictionary containing the results of quantum analysis.
        Returns:
            dict: A dictionary containing the validation results, including whether the
                  code is approved and any violated constraints.
        """
        violations: list[EthicalViolation] = []
        for constraint in self.constraints:
            if constraint.condition(quantum_metrics):
                risk = self.risk_profile.get_risk(constraint.category)
                violations.append(EthicalViolation(constraint, risk))

        approved = len(violations) == 0
        risk_breakdown = self.risk_profile.get_risk_breakdown() if not approved else {}

        return {
            "approved": approved,
            "constraints_violated": [v.to_dict() for v in violations],
            "risk_breakdown": risk_breakdown,
        }

class EthicalAuditLogger:
    """Handles audit trail generation and querying"""

    def __init__(self):
        self.audit_path = "ethical_audits/"
        Path(self.audit_path).mkdir(exist_ok=True)

    def log_decision(self, validation_result: dict):
        """Record ethical validation with quantum state reference"""
        audit_entry = {
            "timestamp": str(datetime.utcnow()),
            "decision": validation_result["approved"],
            "violations": validation_result["constraints_violated"],
            "quantum_state": validation_result["quantum_state_id"],
            "risk_metrics": validation_result["risk_breakdown"],
        }

        with open(f"{self.audit_path}{audit_entry['quantum_state']}.json", "w") as f:
            json.dump(audit_entry, f, indent=2)
