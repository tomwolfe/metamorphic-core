import json
from datetime import datetime
from qiskit import qasm3
from .ethical_validation import EthicalQuantumCore

class QuantumStatePreserver:
    """Preserves quantum circuit states for ethical auditing"""
    
    def __init__(self):
        self.quantum_core = EthicalQuantumCore()
        self.storage_path = "quantum_states/"
    
    def preserve_state(self, code_sample: str) -> str:
        """Save quantum circuit state with timestamped metadata"""
        state_id = f"QSTATE_{datetime.now().strftime('%Y%m%d%H%M%S%f')}"
        qc = self.quantum_core.create_ethical_circuit()
        
        preservation_data = {
            "id": state_id,
            "qasm": qasm3.dumps(qc),
            "timestamp": str(datetime.utcnow()),
            "code_sample": code_sample[:1000],  # Truncate for storage
            "metrics": self.quantum_core.analyze_quantum_state(code_sample)
        }
        
        self._save_to_disk(state_id, preservation_data)
        return state_id
    
    def _save_to_disk(self, state_id: str, data: dict):
        """Save quantum state with error handling"""
        try:
            with open(f"{self.storage_path}{state_id}.json", "w") as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            print(f"State preservation failed: {str(e)}")
