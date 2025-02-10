import os
import pytest
from src.core.ethics.governance import QuantumEthicalValidator
from unittest.mock import patch, MagicMock
from os import environ

@pytest.fixture(scope="module")
def validator():
    """Fixture with valid mock credentials passing SecureConfig checks"""
    valid_mocks = {
        'GEMINI_API_KEY': 'AIzaSy' + 'a'*35,  # 39 chars
        'YOUR_GITHUB_API_KEY': 'ghp_' + 'b'*36,  # 40 chars
        'HUGGING_FACE_API_KEY': 'hf_' + 'c'*31,  # 34 chars
        'ZAP_API_KEY': 'zap_' + 'd'*36,
        'LLM_PROVIDER': 'gemini',
        'LLM_MAX_RETRIES': '3',
        'LLM_TIMEOUT': '30'
    }

    with patch('src.core.agents.security_agent.SecurityAgent.run_zap_baseline_scan') as mock_zap, \
         patch('src.core.agents.test_generator.TestGenAgent.generate_tests') as mock_tests, \
         patch.dict(os.environ, valid_mocks), \
         patch('src.utils.config.SecureConfig.get', lambda x, _=None: valid_mocks.get(x, 'default'))
        
        # Mock agent outputs
        mock_zap.return_value = {'alerts': [], 'scan_id': 'test_scan'}
        mock_tests.return_value = "def test_example(): pass"
        
        yield QuantumEthicalValidator()
 
def test_full_agent_pipeline(validator):
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
