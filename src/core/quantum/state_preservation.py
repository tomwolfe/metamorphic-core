import json
from datetime import datetime
from pathlib import Path
from qiskit import QuantumCircuit
from qiskit.qasm3 import dumps
from .ethical_validation import EthicalQuantumCore

class QuantumStatePreserver:
    """Preserves quantum circuit states for ethical auditing"""
    
    def __init__(self):
        self.quantum_core = EthicalQuantumCore()
        self.storage_path = Path("quantum_states/")
        # Create directory if it doesn't exist
        self.storage_path.mkdir(parents=True, exist_ok=True)
    
    def preserve_state(self, code_sample: str) -> str:
        """Save quantum circuit state with timestamped metadata"""
        state_id = f"QSTATE_{datetime.now().strftime('%Y%m%d%H%M%S%f')}"
        
        # Create valid quantum circuit
        qc = QuantumCircuit(2)
        qc.h(0)
        qc.cx(0, 1)
        
        preservation_data = {
            "id": state_id,
            "qasm": dumps(qc),
            "timestamp": str(datetime.utcnow()),
            "code_sample": code_sample[:1000],
            "metrics": self.quantum_core.analyze_quantum_state(code_sample)
        }
        
        self._save_to_disk(state_id, preservation_data)
        return state_id
    
    def _save_to_disk(self, state_id: str, data: dict):
        """Save quantum state with proper path handling"""
        try:
            file_path = self.storage_path / f"{state_id}.json"
            with file_path.open("w") as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            print(f"State preservation failed: {str(e)}")
