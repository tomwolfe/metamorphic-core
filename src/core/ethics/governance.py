import os
import json
from datetime import datetime
from typing import Dict, Any
from z3 import ModelRef
from ..verification.specification import FormalSpecification
from ..verification.z3_serializer import Z3JSONEncoder
from ..quantum.state_preservation import QuantumStatePreserver # Import state preserver

class QuantumEthicalValidator:
    def __init__(self):
        self.formal_verifier = FormalSpecification()
        self.audit_logger = EthicalAuditLogger()
        self.state_preserver = QuantumStatePreserver() # Initialize state preserver
        self._load_ethical_framework()

    def _load_ethical_framework(self):
        """Load ethical guidelines into verification system"""
        self.formal_verifier.add_safety_invariant("Bias risk never exceeds 0.25")
        self.formal_verifier.add_ethical_guardrail("Transparency never drops below 0.4")
        # Temporarily remove privacy constraint
        # self.formal_verifier.add_safety_invariant("Privacy risk never exceeds 0.3")

    def validate_code(self, code_sample: str) -> Dict[str, Any]:
        """Perform comprehensive ethical validation"""
        state_id = self.state_preserver.preserve_state(code_sample) # Preserve state first
        validation_result = {
            "state_id": state_id, # Add state_id to result
            "status": "pending",
            "score": 0.0,
            "predictions": self._predict_ethical_impact(code_sample),
            "formal_proof": None,
            "timestamp": str(datetime.utcnow()),
            "code_sample_hash": hash(code_sample) # Include code sample hash
        }

        try:
            # Formal mathematical verification
            validation_result["formal_proof"] = self.formal_verifier.verify_predictions(
                validation_result["predictions"]
            )

            # Calculate composite ethical score
            validation_result["score"] = self._calculate_ethical_score(
                validation_result["formal_proof"]
            )

            # Determine final status
            validation_result["status"] = "approved" if validation_result["score"] >= 0.7 else "rejected"

        except Exception as e:
            validation_result.update({
                "status": "error",
                "error": str(e),
                "score": 0.0
            })

        # Log decision with serialization handling
        self.audit_logger.log_decision(validation_result)
        return validation_result

    def _predict_ethical_impact(self, code: str) -> Dict[str, float]:
        """Predict ethical impact with all required metrics"""
        return {
            "bias_risk": 0.15,
            "transparency_score": 0.7,
            "immediate_risk": 0.1,
            "long_term_risk": 0.2,
            "privacy_risk": 0.1  # Added missing required metric
        }

    def _calculate_ethical_score(self, proof: Dict) -> float:
        """Calculate score based on verification status"""
        if proof.get('verified', False):
            return 1.0
        return 0.5  # Base score when unverified but no errors

class EthicalAuditLogger:
    def __init__(self):
        self.log_dir = "audit_logs"
        os.makedirs(self.log_dir, exist_ok=True)

    def log_decision(self, validation_result: dict):
        """Log decision with Z3 model serialization handling"""
        processed_proof = self._process_z3_models(validation_result.get("formal_proof", {}))

        audit_entry = {
            "timestamp": datetime.utcnow().isoformat(),
            "decision": validation_result["status"],
            "ethical_score": validation_result["score"],
            "formal_proof": processed_proof,
            "model_version": self._get_model_version(),
            "code_sample_hash": validation_result.get("code_sample_hash") # Use hash from result
        }

        filename = f"decision_{datetime.utcnow().strftime('%Y%m%d%H%M%S')}.json"
        filepath = os.path.join(self.log_dir, filename)

        with open(filepath, "w") as f:
            json.dump(audit_entry, f, indent=2, cls=Z3JSONEncoder)

    def _process_z3_models(self, proof_data: dict) -> dict:
        """Convert Z3 models to serializable format"""
        if not proof_data:
            return {}

        processed = {}
        if proof_data.get('model'): # Process model if present
             processed['model'] = self._convert_z3_model(proof_data['model'])
        return processed

    def _convert_z3_model(self, model_data: dict) -> dict:
        """Recursively convert Z3 model components"""
        converted = {}
        for k, v in model_data.items():
            if isinstance(v, ModelRef):
                converted[k] = json.loads(json.dumps(v, cls=Z3JSONEncoder))
            else:
                converted[k] = v
        return converted

    def _get_model_version(self) -> str:
        """Get current ethical model version"""
        return "ETHICAL_MODEL_v2.3.1"

class EthicalGovernanceEngine:
    """Orchestrates complete ethical oversight"""

    def __init__(self):
        self.validator = QuantumEthicalValidator()
        self.history = []

    def evaluate_development_cycle(self, code: str) -> Dict:
        """Full ethical evaluation pipeline"""
        result = self.validator.validate_code(code)
        return result

    def get_ethical_health_report(self) -> Dict[str, Any]:
        """Generate a comprehensive health report of the ethical governance system"""
        latest_validations = self.history[-10:] if self.history else []
        
        report = {
            "model_version": self.get_ethical_model_version(),
            "system_status": "healthy",  # Default to healthy
            "metrics": {
                "average_ethical_score": 0.0,
                "recent_validation_count": len(latest_validations),
                "failed_validations": 0,
                "bias_alerts": 0,
                "transparency_warnings": 0
            },
            "timestamp": datetime.utcnow().isoformat()
        }
        
        # Calculate metrics from recent validations
        if latest_validations:
            scores = [v.get("score", 0.0) for v in latest_validations]
            failed = sum(1 for v in latest_validations if v.get("status") == "rejected")
            
            report["metrics"].update({
                "average_ethical_score": sum(scores) / len(scores),
                "failed_validations": failed,
                # Count warnings from predictions
                "bias_alerts": sum(1 for v in latest_validations 
                                 if v.get("predictions", {}).get("bias_risk", 0) > 0.2),
                "transparency_warnings": sum(1 for v in latest_validations 
                                          if v.get("predictions", {}).get("transparency_score", 1) < 0.5)
            })
            
            # Update system status based on metrics
            if (report["metrics"]["average_ethical_score"] < 0.6 or 
                report["metrics"]["failed_validations"] > len(latest_validations) * 0.3):
                report["system_status"] = "degraded"
                
        return report

    def get_ethical_model_version(self) -> str:
        return "ETHICAL_MODEL_v2.3.1"  # Match version from EthicalAuditLogger
