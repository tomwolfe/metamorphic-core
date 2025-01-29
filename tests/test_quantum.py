# tests/test_quantum.py
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from unittest.mock import patch, MagicMock
import pytest
from qiskit.primitives import SamplerResult
from src.core.quantum.ethical_validation import EthicalQuantumCore

@pytest.fixture
def mock_sampler():
    mock = MagicMock()
    mock.run.return_value = MagicMock()
    mock.run.return_value.result.return_value = SamplerResult(
        quasi_dists=[{0: 0.4, 1: 0.6}], 
        metadata=[{}]
    )
    return mock

# Update the mock targets to use StatevectorSampler
def test_quantum_analysis_with_mocks(mock_sampler):
    with patch('qiskit.primitives.StatevectorSampler', return_value=mock_sampler):
        core = EthicalQuantumCore()
        result = core.analyze_quantum_state("test")

def test_quantum_error_handling():
    with patch('qiskit.primitives.StatevectorSampler') as mock_sampler:
        mock_sampler.side_effect = Exception("Quantum backend unreachable")
        core = EthicalQuantumCore()
        result = core.analyze_quantum_state("test")
