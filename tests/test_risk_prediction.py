# tests/test_risk_prediction.py
from unittest.mock import patch, MagicMock
import pytest
import numpy as np
from src.core.prediction.risk_model import QuantumRiskPredictor

@pytest.fixture
def mock_sampler():
    mock = MagicMock()
    mock.run.return_value = MagicMock()
    mock.run.return_value.result.return_value.quasi_dists = [{0: 0.8}]
    return mock
    
def test_risk_prediction(mock_sampler):
    with patch('qiskit.primitives.Sampler', return_value=mock_sampler):
        predictor = QuantumRiskPredictor(num_qubits=2)
        
        # Wrap mock data in a list of sequences
        mock_data = [
            [{'risk_metrics': {  # Note the list containing a single entry
                'bias_risk': 0.1,
                'safety_risk': 0.2,
                'transparency_score': 0.8,
                'composite_risk': 0.15
            }}]
        ]
        
        predictor.train(mock_data)
        prediction = predictor.predict_risk(mock_data[0][0])  # Access first entry
