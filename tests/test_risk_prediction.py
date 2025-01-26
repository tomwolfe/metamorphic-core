# tests/test_risk_prediction.py
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import pytest
from src.core.prediction.risk_model import QuantumRiskPredictor

def test_risk_prediction_with_sample_data():
    predictor = QuantumRiskPredictor()
    mock_data = [
        {
            "risk_metrics": {
                "bias_risk": 0.1,
                "safety_risk": 0.2,
                "composite_risk": 0.15
            }
        }
    ]
    predictor.train(mock_data)
    prediction = predictor.predict_risk(mock_data[0])
    assert isinstance(prediction, float)
    assert 0 <= prediction <= 1
