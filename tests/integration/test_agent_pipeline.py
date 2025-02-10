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
    
    with patch('src.utils.config.SecureConfig.get') as mock_get, \
         patch('src.utils.config.SecureConfig.load'), \
         patch.dict(os.environ, valid_mocks):
        
        mock_get.side_effect = lambda var, default=None: valid_mocks.get(var)
        yield QuantumEthicalValidator()
             
def test_full_agent_pipeline(validator):
    code = "def example(): pass"
    result = validator.validate_code(code)
    assert 'spec_analysis' in result
    assert 'security_scan' in result
    assert 'code_review' in result
    assert 'generated_tests' in result
            
    kg = KnowledgeGraph()
    nodes = kg.search("code_review")
    assert any(n.type == "code_review" for n in nodes)
    
    # Test score calculation
    assert 0 <= result['score'] <= 1
    if result['score'] < 0.7:
        assert result['status'] == "rejected"
    else:
        assert result['status'] == "approved"
