from qiskit import QuantumCircuit
from qiskit.primitives import StatevectorSampler
import numpy as np

class EthicalQuantumCore:
    def __init__(self):
        self._ethical_weights = {
            'bias': 0.5, 
            'safety': 0.5,
            'transparency': 0.5
        }
        try:
            self.sampler = StatevectorSampler()
        except Exception as e:
            self.sampler = None
            self._error = str(e)
            
    def analyze_quantum_state(self, code_hash: str) -> dict:
        if not self.sampler:
            return {"error": f"Quantum init failed: {self._error}", "basis_states": {}}
        try:
            qc = self.create_ethical_circuit()
            job = self.sampler.run([qc], shots=1000)  # V2 requires list input
            result = job.result()
            pub_result = result[0]
            
            # Get counts as integer dictionary
            counts = pub_result.data.meas.get_counts()
            total_shots = sum(counts.values())
            
            # Convert integer keys to 3-bit binary strings
            basis_states = {
                f"{state:03b}": count for state, count in counts.items()
            }
            
            return {
                'basis_states': basis_states,
                'bias_prob': counts.get(0b100, 0) / total_shots,
                'safety_prob': counts.get(0b010, 0) / total_shots,
                'transparency_prob': counts.get(0b001, 0) / total_shots
            }
        except Exception as e:
            return {
                'error': f"Quantum analysis failed: {str(e)}",
                'basis_states': {}
            }
            
    def create_ethical_circuit(self) -> QuantumCircuit:
        """Generate quantum circuit representing ethical decision weights"""
        qc = QuantumCircuit(3)
        # Initialize qubits with valid quantum states
        qc.initialize([np.sqrt(self._ethical_weights['bias']), 
                      np.sqrt(1 - self._ethical_weights['bias'])], 0)
        qc.initialize([np.sqrt(self._ethical_weights['safety']),
                      np.sqrt(1 - self._ethical_weights['safety'])], 1)
        qc.cx(0, 1)
        qc.cx(1, 2)
        qc.measure_all()  # Explicit measurement for sampling
        return qc
