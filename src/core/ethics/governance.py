from pathlib import Path
from typing import Dict, List
import json
from datetime import datetime
from hashlib import sha256
from ..quantum.state_preservation import QuantumStatePreserver
from .constraints import (
    EthicalConstraint,
    ConstraintCategory,
    RiskProfile,
    EthicalViolation,
    CORE_CONSTRAINTS  # Added from constraints.py
)
from ..quantum.ethical_validation import EthicalQuantumCore  # Changed import

class QuantumEthicalValidator:
    """Applies ethical constraints to quantum code analysis results."""

    def __init__(self, constraints: List[EthicalConstraint] = None):
        self.constraints = constraints or CORE_CONSTRAINTS  # Use default constraints
        self.quantum_analyzer = EthicalQuantumCore()  # Changed to correct class
        self.state_preserver = QuantumStatePreserver()

    def _hash_code(self, code_sample: str) -> str:
        """Creates a SHA-256 hash of the code sample for anonymity."""
        return sha256(code_sample.encode()).hexdigest()

    def validate_code(self, code_sample: str) -> Dict:
        """Full validation pipeline with quantum state preservation"""
        quantum_metrics = self.quantum_analyzer.analyze_quantum_state(
            self._hash_code(code_sample)
        )
        
        if 'error' in quantum_metrics:
            return {
                'approved': False,
                'error': quantum_metrics['error'],
                'constraints_violated': ['system_error']
            }

        state_id = self.state_preserver.preserve_state(code_sample)
        validation_result = self._apply_ethical_rules(quantum_metrics)
        validation_result["quantum_state_id"] = state_id
        return validation_result

    def add_constraint(self, constraint: EthicalConstraint):
        """Adds a new ethical constraint to the validator."""
        self.constraints.append(constraint)

    def _apply_ethical_rules(self, quantum_metrics: dict) -> dict:
        """Applies ethical constraints based on quantum analysis results."""
        violations = []
        
        for constraint in self.constraints:
            if constraint.category == ConstraintCategory.BIAS:
                if quantum_metrics['bias_prob'] > constraint.quantum_weight:
                    violations.append(EthicalViolation(
                        constraint=constraint,
                        violation_timestamp=datetime.utcnow(),
                        severity=quantum_metrics['bias_prob'],
                        quantum_state_id="N/A"  # Will be updated later
                    ))
                    
            elif constraint.category == ConstraintCategory.SAFETY:
                if quantum_metrics['safety_prob'] > constraint.quantum_weight:
                    violations.append(EthicalViolation(
                        constraint=constraint,
                        violation_timestamp=datetime.utcnow(),
                        severity=quantum_metrics['safety_prob'],
                        quantum_state_id="N/A"
                    ))
                    
            elif constraint.category == ConstraintCategory.TRANSPARENCY:
                if quantum_metrics['transparency_prob'] < constraint.quantum_weight:
                    violations.append(EthicalViolation(
                        constraint=constraint,
                        violation_timestamp=datetime.utcnow(),
                        severity=quantum_metrics['transparency_prob'],
                        quantum_state_id="N/A"
                    ))

        return {
            "approved": len(violations) == 0,
            "constraints_violated": [v.dict() for v in violations],
            "risk_breakdown": {
                'bias_risk': quantum_metrics.get('bias_prob', 0),
                'safety_risk': quantum_metrics.get('safety_prob', 0),
                'transparency_score': quantum_metrics.get('transparency_prob', 0)
            }
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
            "violations": [v for v in validation_result["constraints_violated"]],
            "quantum_state": validation_result["quantum_state_id"],
            "risk_metrics": validation_result["risk_breakdown"]
        }

        # Update violations with actual state ID
        for violation in audit_entry["violations"]:
            violation["quantum_state_id"] = audit_entry["quantum_state"]

        with open(f"{self.audit_path}{audit_entry['quantum_state']}.json", "w") as f:
            json.dump(audit_entry, f, indent=2)
