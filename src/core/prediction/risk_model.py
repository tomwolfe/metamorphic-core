# File: src/core/prediction/risk_model.py
from qiskit.circuit import ParameterVector, QuantumCircuit
from qiskit.primitives import StatevectorSampler  # Use V2 primitive compatible with Qiskit 1.x
from scipy.optimize import minimize # Import minimize from scipy
from qiskit_machine_learning.neural_networks import SamplerQNN # RESTORED import
import numpy as np
from sklearn.preprocessing import MinMaxScaler
import logging

logger = logging.getLogger(__name__)

class QuantumRiskPredictor:
    """
    Quantum-enhanced risk prediction using modern Qiskit primitives.
    Uses SamplerQNN from qiskit-machine-learning.
    """

    def __init__(self, num_qubits=4):
        # logger.warning("QuantumRiskPredictor initialized, but QNN functionality is disabled due to dependency incompatibility.") # Removed warning
        self.sampler = StatevectorSampler() # Use V2 primitive
        self.num_qubits = num_qubits
        self.scaler = MinMaxScaler()
        self.optimal_weights = None # Initialize optimal_weights

        # Quantum neural network setup - RESTORED
        self.qnn = self._create_qnn()

    def _create_qnn(self):
        """
        Create parameterized quantum circuit and SamplerQNN instance. RESTORED.
        """
        # logger.error("Attempted to create QNN, but qiskit-machine-learning is not installed/used.") # Removed error
        # raise NotImplementedError("QNN creation is disabled due to dependency incompatibility.") # Removed error
        # Original code restored and adapted:
        params = ParameterVector('input', self.num_qubits)
        feature_map = QuantumCircuit(self.num_qubits, name="FeatureMap") # Added name
        for qubit in range(self.num_qubits):
            feature_map.h(qubit)
            feature_map.ry(params[qubit], qubit)

        ansatz = QuantumCircuit(self.num_qubits, name="Ansatz") # Added name
        ansatz_params = ParameterVector('weights', self.num_qubits) # Example: Add parameters to ansatz
        for qubit in range(self.num_qubits-1):
            ansatz.cx(qubit, qubit+1)
        for qubit in range(self.num_qubits): # Example: Add rotation with weights
             ansatz.rz(ansatz_params[qubit], qubit)

        # Combine feature map and ansatz
        full_circuit = feature_map.compose(ansatz)

        # SamplerQNN expects a callable for interpret function in newer versions
        # Default interpret maps output probabilities to labels {0, 1} based on parity.
        # Adjust if your risk prediction needs raw probabilities or different mapping.
        def parity(x):
             return "{:b}".format(x).count("1") % 2

        return SamplerQNN(
            sampler=self.sampler, # Use the V2 sampler
            circuit=full_circuit,
            input_params=feature_map.parameters,
            weight_params=ansatz.parameters,
            interpret=parity, # Default interpret function (maps to 0 or 1)
            output_shape=2, # Output shape for binary classification (adjust if needed)
            input_gradients=True # Optional: for gradient-based optimization
        )


    def train(self, historical_data: list):
        """
        Training functionality using SamplerQNN. RESTORED.
        """
        # logger.error("Training attempted, but QNN functionality is disabled.") # Removed error
        # raise NotImplementedError("Training is disabled due to dependency incompatibility.") # Removed error
        # Original code restored and adapted:
        X, y = self._preprocess_data(historical_data)
        if X.size == 0:
             logger.warning("Training skipped: No preprocessed data available.")
             return

        def cost_function(weights):
            # QNN forward pass for SamplerQNN returns probabilities for each class (shape depends on output_shape)
            # Input X might need reshaping depending on QNN expectations
            predictions = self.qnn.forward(X, weights)
            # Assuming binary classification (output_shape=2) and y contains labels {0, 1}
            # We need to compare predicted probabilities (e.g., prob of class 1) with labels y
            # Example: Use probability of class 1 for loss calculation
            prob_class_1 = predictions[:, 1] # Assuming second column is prob of class 1
            return np.mean((prob_class_1 - y)**2) # Simple MSE loss against labels

        initial_weights = np.random.rand(self.qnn.num_weights)
        result = minimize(
             fun=cost_function,
             x0=initial_weights,
             method='COBYLA',
             options={'maxiter': 100}
        )
        self.optimal_weights = result.x

    def predict_risk(self, current_state: dict) -> float:
        """
        Risk prediction using trained SamplerQNN. RESTORED.
        Returns the predicted probability of the positive class (risk).
        """
        # logger.warning("Predict_risk called, but QNN functionality is disabled. Returning placeholder 0.0.") # Removed warning
        # return 0.0 # Removed placeholder
        # Original code restored and adapted:
        if self.optimal_weights is None:
            raise RuntimeError("Model has not been trained yet. Call train() first.")

        processed_input = self._process_current_state(current_state)
        # Ensure input has the correct shape for QNN (e.g., (1, num_features))
        input_scaled = self.scaler.transform(np.array(processed_input).reshape(1, -1))

        # QNN forward pass returns probabilities (e.g., shape (1, 2) for binary)
        probabilities = self.qnn.forward(input_scaled, self.optimal_weights)

        # Return the probability of the "risky" class (e.g., class 1)
        # Adjust index [0, 1] if your interpretation differs
        risk_probability = probabilities[0, 1]

        return float(risk_probability)

    # _preprocess_data, _process_current_state, _extract_temporal_features remain the same as in the previous response
    # (with the fix for empty data handling in _preprocess_data)
    def _preprocess_data(self, data: list):
        """Convert audit trails to temporal features (kept for potential future use)"""
        features = np.array([
            self._extract_temporal_features(seq)
            for seq in data if seq # Ensure sequence is not empty
        ])
        # Ensure labels correspond to the filtered features and handle potential missing keys
        labels = []
        valid_features_indices = []
        for i, seq in enumerate(data):
             if seq and 'risk_metrics' in seq[-1] and 'composite_risk' in seq[-1]['risk_metrics']:
                 labels.append(seq[-1]['risk_metrics']['composite_risk'])
                 valid_features_indices.append(i)

        if not valid_features_indices:
             logger.warning("Preprocessing resulted in empty features or labels due to missing data.")
             return np.array([]), np.array([])

        # Filter features to match valid labels
        features = features[valid_features_indices]
        labels = np.array(labels)


        if features.size == 0 or labels.size == 0:
             logger.warning("Preprocessing resulted in empty features or labels.")
             return np.array([]), np.array([])

        if features.shape[0] != labels.shape[0]:
            # This case should ideally not happen if filtering is correct, but handle defensively
            logger.error(f"CRITICAL: Mismatch between number of feature samples ({features.shape[0]}) and label samples ({labels.shape[0]}) after filtering.")
            min_len = min(features.shape[0], labels.shape[0])
            return self.scaler.fit_transform(features[:min_len]), labels[:min_len]


        return self.scaler.fit_transform(features), labels

    def _process_current_state(self, state: dict):
        """Convert real-time state to model input (kept for potential future use)"""
        features = self._extract_temporal_features([state])
        return features

    def _extract_temporal_features(self, sequence: list):
        """Feature engineering from audit sequences (kept for potential future use)"""
        if not sequence:
            return [0.0] * self.num_qubits

        last_entry = sequence[-1]
        risk_metrics = last_entry.get('risk_metrics', {})

        bias_risk = risk_metrics.get('bias_risk', 0.0)
        safety_risk = risk_metrics.get('safety_risk', 0.0)
        transparency_score_mean = np.mean([
            e.get('risk_metrics', {}).get('transparency_score', 0.0)
            for e in sequence if isinstance(e, dict)
        ]) if sequence else 0.0

        features = [
            bias_risk,
            safety_risk,
            len(sequence) / 10.0, # Example normalization
            transparency_score_mean
        ]

        # Pad or truncate features if necessary to match num_qubits
        if len(features) > self.num_qubits:
            features = features[:self.num_qubits]
        elif len(features) < self.num_qubits:
            features.extend([0.0] * (self.num_qubits - len(features)))

        return features