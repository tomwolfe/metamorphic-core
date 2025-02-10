import os
import pytest
from src.core.ethics.governance import QuantumEthicalValidator
from unittest.mock import patch, MagicMock

@pytest.fixture
def valid_mocks():
    return {
        'GEMINI_API_KEY': 'AIzaSy' + 'a' * 32,  # 39 chars (meet minimum)
        'YOUR_GITHUB_API_KEY': 'ghp_' + 'a' * 40,  # 44 chars (meet GitHub API key format)
        'HUGGING_FACE_API_KEY': 'hf_' + 'a' * 30,  # 34 chars (meet Hugging Face requirements)
        'ZAP_API_KEY': 'zap_' + 'a' * 36,
        'LLM_PROVIDER': 'gemini',
        'LLM_MAX_RETRIES': '3',
        'LLM_TIMEOUT': '30',
    }

@pytest.fixture
def mock_config(valid_mocks, monkeypatch):
    """Fixture with valid mock credentials passing SecureConfig checks"""
    with (
        patch('src.core.agents.security_agent.SecurityAgent.run_zap_baseline_scan') as mock_zap,
        patch('src.core.agents.test_generator.TestGenAgent.generate_tests') as mock_tests,
        monkeypatch.context() as m
    ):
        m.setattr(os, 'environ', valid_mocks)
        mock_zap.return_value = {'alerts': [], 'scan_id': 'test_scan'}
        mock_tests.return_value = "def test_example(): pass"
        yield

def test_full_agent_pipeline(mock_config):
    validator = QuantumEthicalValidator()
    code = "def example(): pass"
    result = validator.validate_code(code)

    # Verify all agents were called
    assert isinstance(result['spec_analysis'], dict)
    assert isinstance(result['security_scan'], dict)
    assert isinstance(result['code_review'], dict)
    assert isinstance(result['generated_tests'], str)

    # Verify basic structure of outputs
    assert 'functions' in result['spec_analysis']
    assert 'alerts' in result['security_scan']
    assert 'static_analysis' in result['code_review']
