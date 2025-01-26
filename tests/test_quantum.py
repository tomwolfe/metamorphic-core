# tests/test_quantum.py
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

def test_quantum_analysis_with_mocks(mock_sampler):
    with patch('src.core.quantum.ethical_validation.Sampler', return_value=mock_sampler):
        core = EthicalQuantumCore()
        result = core.analyze_quantum_state("test")
        
    assert 'basis_states' in result
    assert sum(result['basis_states'].values()) == 1000  # Validate shot normalization
