import pytest
from unittest.mock import patch, MagicMock
import numpy as np
from src.core.prediction.risk_model import QuantumRiskPredictor

@pytest.fixture
def mock_sampler():
    mock = MagicMock()
    mock.run.return_value = MagicMock()
    mock.run.return_value.result.return_value.quasi_dists = [{0: 0.8}]
    return mock

def test_risk_prediction_with_mocks(mock_sampler):
    with patch('qiskit.primitives.Sampler', return_value=mock_sampler):
        predictor = QuantumRiskPredictor()
        
        # Mock historical data format
        mock_data = [
            {"risk_metrics": {
                "bias_risk": 0.1,
                "safety_risk": 0.2,
                "composite_risk": 0.15
            }}
        ]
        
        # Test training and prediction
        predictor.train(mock_data)
        prediction = predictor.predict_risk(mock_data[0])
        
        assert 0 <= prediction <= 1
        mock_sampler.run.assert_called()  # Verify quantum execution
