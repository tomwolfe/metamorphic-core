# File: src/core/prediction/risk_model.py
from qiskit.circuit import ParameterVector, QuantumCircuit
from qiskit.primitives import StatevectorSampler  # Updated to V2 primitive
from qiskit_algorithms.optimizers import COBYLA
from qiskit_machine_learning.neural_networks import SamplerQNN
import numpy as np
from sklearn.preprocessing import MinMaxScaler

class QuantumRiskPredictor:
    """Quantum-enhanced risk prediction using modern Qiskit primitives"""
    
    def __init__(self, num_qubits=4):
        self.sampler = StatevectorSampler()  # V2 primitive
        self.num_qubits = num_qubits
        self.scaler = MinMaxScaler()
        
        # Quantum neural network setup
        self.qnn = self._create_qnn()
        self.optimizer = COBYLA(maxiter=100)
        
    def _create_qnn(self):
        """Create parameterized quantum circuit with V2 integration"""
        params = ParameterVector('input', self.num_qubits)
        feature_map = QuantumCircuit(self.num_qubits)
        for qubit in range(self.num_qubits):
            feature_map.h(qubit)
            feature_map.ry(params[qubit], qubit)
        
        ansatz = QuantumCircuit(self.num_qubits)
        for qubit in range(self.num_qubits-1):
            ansatz.cx(qubit, qubit+1)
        
        return SamplerQNN(
            sampler=self.sampler,
            circuit=feature_map.compose(ansatz),
            input_params=feature_map.parameters,
            weight_params=ansatz.parameters,
            input_gradients=True
        )
    
    def train(self, historical_data: list):
        """Train using V2-compatible approach"""
        X, y = self._preprocess_data(historical_data)
        
        def cost_function(weights):
            # Get predictions directly from QNN forward pass
            predictions = self.qnn.forward(X, weights)
            return np.mean((predictions - y)**2)
        
        initial_weights = np.random.rand(self.qnn.num_weights)
        self.optimal_weights = self.optimizer.minimize(
            fun=cost_function,
            x0=initial_weights
        ).x

    def predict_risk(self, current_state: dict) -> float:
        """Predict risk using V2 primitive results"""
        processed_input = self._process_current_state(current_state)
        input_scaled = self.scaler.transform([processed_input])
    
        # Convert numpy array to scalar
        probabilities = self.qnn.forward(input_scaled, self.optimal_weights)
        return float(probabilities[0, 0])  # Access the first element of the array
        
    def _preprocess_data(self, data: list):
        """Convert audit trails to temporal features"""
        # Feature engineering from historical sequences
        features = np.array([
            self._extract_temporal_features(seq) 
            for seq in data
        ])
        labels = np.array([seq[-1]['risk_metrics']['composite_risk'] for seq in data])
        
        return self.scaler.fit_transform(features), labels
    
    def _process_current_state(self, state: dict):
        """Convert real-time state to model input"""
        features = self._extract_temporal_features([state])
        return self.scaler.transform([features])[0]
    
    def _extract_temporal_features(self, sequence: list):
        """Feature engineering from audit sequences"""
        if not sequence:
            return [0.0] * 4  # Return zero-filled features for empty sequence
        
        last_entry = sequence[-1].get('risk_metrics', {})
        return [
            last_entry.get('bias_risk', 0.0),
            last_entry.get('safety_risk', 0.0),
            len(sequence),
            np.mean([e.get('risk_metrics', {}).get('transparency_score', 0.0) for e in sequence])
        ]
