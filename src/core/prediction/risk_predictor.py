from qiskit import QuantumCircuit, transpile
from qiskit.circuit import ParameterVector
from qiskit.circuit.library import RealAmplitudes
from qiskit_aer import Aer
import numpy as np

class QuantumRiskPredictor:
    """Quantum risk predictor with exact parameter matching"""
    
    def __init__(self, num_qubits=3, time_steps=5):
        self.num_qubits = num_qubits
        self.time_steps = time_steps
        self.backend = Aer.get_backend('aer_simulator')
        self._build_circuit()

    def _build_circuit(self):
        """Build circuit with precise parameter count"""
        # Calculate exact parameter requirements
        num_rotations = self.num_qubits
        var_form = RealAmplitudes(self.num_qubits, reps=1)
        total_params = num_rotations + len(var_form.parameters)
        
        self.params = ParameterVector('θ', length=total_params)
        
        # Build circuit
        self.circuit = QuantumCircuit(self.num_qubits)
        
        # Rotation layer
        for i in range(self.num_qubits):
            self.circuit.ry(self.params[i], i)
        
        # Entanglement
        for i in range(self.num_qubits-1):
            self.circuit.cx(i, i+1)
            
        # Variational form with exact parameter mapping
        param_mapping = {
            param: self.params[i + self.num_qubits] 
            for i, param in enumerate(var_form.parameters)
        }
        self.circuit.compose(
            var_form.assign_parameters(param_mapping),
            inplace=True
        )
        
        self.circuit.measure_all()

    def forecast_risk(self, history: list) -> dict:
        """Quantum risk prediction with safe parameter binding"""
        processed_data = self._preprocess(history)
        param_bind = {
            param: processed_data[i % len(processed_data)]
            for i, param in enumerate(self.params)
        }
        transpiled = transpile(
            self.circuit.assign_parameters(param_bind),
            self.backend,
            optimization_level=1
        )
        job = self.backend.run(transpiled, shots=1000)
        counts = job.result().get_counts()
        
        return {
            'immediate': counts.get('0'*self.num_qubits, 0)/1000,
            'short_term': np.mean(list(counts.values()))/1000,
            'long_term': max(counts.values())/1000
        }

    def _preprocess(self, data: list) -> np.ndarray:
        """Ensure valid input data dimensions"""
        base_data = np.array([
            [entry.get('bias_risk', 0.0), 
             entry.get('safety_risk', 0.0),
             entry.get('transparency_score', 0.5)]
            for entry in data[-self.time_steps:]
        ]).flatten() / 2.0
        
        # Pad/cut to match required parameter count
        target_length = len(self.params)
        return np.pad(
            base_data,
            (0, max(0, target_length - len(base_data))),
            mode='constant',
            constant_values=0.25
        )[:target_length]
