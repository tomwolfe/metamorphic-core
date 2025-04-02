# File: src/core/prediction/risk_model.py
from qiskit.circuit import ParameterVector, QuantumCircuit
from qiskit.primitives import StatevectorSampler  # Updated to V2 primitive
from scipy.optimize import minimize # Import minimize from scipy
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
        # self.optimizer = COBYLA(maxiter=100) # COBYLA is used via scipy.optimize.minimize
        self.optimal_weights = None # Initialize optimal_weights

    def _create_qnn(self):
        """Create parameterized quantum circuit with V2 integration"""
        params = ParameterVector('input', self.num_qubits)
        feature_map = QuantumCircuit(self.num_qubits)
        for qubit in range(self.num_qubits):
            feature_map.h(qubit)
            feature_map.ry(params[qubit], qubit)

        ansatz = QuantumCircuit(self.num_qubits)
        # Ensure ansatz has parameters if qnn expects them
        ansatz_params = ParameterVector('weights', self.num_qubits) # Example: Add parameters to ansatz
        for qubit in range(self.num_qubits-1):
            ansatz.cx(qubit, qubit+1)
        for qubit in range(self.num_qubits): # Example: Add rotation with weights
             ansatz.rz(ansatz_params[qubit], qubit)


        # Combine feature map and ansatz
        full_circuit = feature_map.compose(ansatz)

        return SamplerQNN(
            sampler=self.sampler,
            circuit=full_circuit, # Use combined circuit
            input_params=feature_map.parameters,
            weight_params=ansatz.parameters, # Use ansatz parameters as weights
            input_gradients=True
        )

    def train(self, historical_data: list):
        """Train using V2-compatible approach"""
        X, y = self._preprocess_data(historical_data)

        def cost_function(weights):
            # Get predictions directly from QNN forward pass
            # Ensure input X is correctly shaped if needed by QNN
            predictions = self.qnn.forward(X, weights)
            # Ensure predictions and y are compatible for loss calculation
            # QNN might return probabilities, adjust loss accordingly if y is not probability
            return np.mean((predictions - y)**2) # Simple MSE loss

        # Use scipy.optimize.minimize with COBYLA method
        initial_weights = np.random.rand(self.qnn.num_weights)
        result = minimize(
            fun=cost_function,
            x0=initial_weights,
            method='COBYLA',
            options={'maxiter': 100}
        )
        self.optimal_weights = result.x # Store the optimal weights found by the optimizer

    def predict_risk(self, current_state: dict) -> float:
        """Predict risk using V2 primitive results"""
        if self.optimal_weights is None:
            raise RuntimeError("Model has not been trained yet. Call train() first.")

        processed_input = self._process_current_state(current_state)
        input_scaled = self.scaler.transform([processed_input])

        # Convert numpy array to scalar probability if needed
        # QNN forward might return an array, e.g., [[prob_class_0, prob_class_1]]
        # Adjust indexing based on QNN output format and what 'risk' represents
        probabilities = self.qnn.forward(input_scaled, self.optimal_weights)

        # Assuming QNN output is shape (1, num_classes) or similar,
        # and risk corresponds to the probability of the first class/state.
        # Adjust this logic based on your specific QNN output interpretation.
        if probabilities.ndim > 1:
             risk_probability = probabilities[0, 0] # Example: take first element of first row
        else:
             risk_probability = probabilities[0] # Example: take first element if 1D array

        return float(risk_probability)

    def _preprocess_data(self, data: list):
        """Convert audit trails to temporal features"""
        # Feature engineering from historical sequences
        features = np.array([
            self._extract_temporal_features(seq)
            for seq in data if seq # Ensure sequence is not empty
        ])
        # Ensure labels correspond to the filtered features
        labels = np.array([
            seq[-1]['risk_metrics']['composite_risk']
            for seq in data if seq and 'risk_metrics' in seq[-1] and 'composite_risk' in seq[-1]['risk_metrics']
        ])

        if features.size == 0 or labels.size == 0:
             raise ValueError("Preprocessing resulted in empty features or labels. Check input data.")

        # Ensure features and labels have the same number of samples
        if features.shape[0] != labels.shape[0]:
            raise ValueError(f"Mismatch between number of feature samples ({features.shape[0]}) and label samples ({labels.shape[0]})")


        return self.scaler.fit_transform(features), labels

    def _process_current_state(self, state: dict):
        """Convert real-time state to model input"""
        # Ensure the input state structure matches what _extract_temporal_features expects
        # It expects a list of states (a sequence), so wrap the single state in a list
        features = self._extract_temporal_features([state])
        # Since scaler expects 2D array, reshape features if necessary or ensure _extract returns suitable shape
        # The scaler was fit on potentially multiple features, transform expects same number.
        # If features is 1D, reshape: features.reshape(1, -1)
        return features # Return the extracted features directly

    def _extract_temporal_features(self, sequence: list):
        """Feature engineering from audit sequences"""
        if not sequence:
            # Return features consistent with the number of qubits/input params
            return [0.0] * self.num_qubits # Match num_qubits

        # Ensure the last entry and its nested dictionaries/keys exist
        last_entry = sequence[-1]
        risk_metrics = last_entry.get('risk_metrics', {})

        # Extract features, providing defaults if keys are missing
        bias_risk = risk_metrics.get('bias_risk', 0.0)
        safety_risk = risk_metrics.get('safety_risk', 0.0)
        transparency_score_mean = np.mean([
            e.get('risk_metrics', {}).get('transparency_score', 0.0)
            for e in sequence if isinstance(e, dict) # Check if e is a dict
        ]) if sequence else 0.0

        # Construct the feature vector - ensure it matches num_qubits
        # Example: if num_qubits is 4, provide 4 features
        features = [
            bias_risk,
            safety_risk,
            len(sequence) / 10.0, # Normalize sequence length (example)
            transparency_score_mean
        ]

        # Pad or truncate features if necessary to match num_qubits
        if len(features) > self.num_qubits:
            features = features[:self.num_qubits]
        elif len(features) < self.num_qubits:
            features.extend([0.0] * (self.num_qubits - len(features)))

        return features
