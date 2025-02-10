import pytest
from unittest.mock import patch, MagicMock
from src.core.ethics.governance import QuantumEthicalValidator

@pytest.fixture(scope="module")
def validator():
    # Mock environment variables with valid patterns
    mock_env_vars = {
        'GEMINI_API_KEY': 'AIzaSyA1234567890abcdefghijklmnopqrstuvwxyz',
        'YOUR_GITHUB_API_KEY': 'ghp_abcdefghijklmnopqrstuvwxyz123456',
        'HUGGING_FACE_API_KEY': 'hf_abcdefghijklmnopqrstuvwxyz123456',
        'ZAP_API_KEY': 'test_zap_key',
        'LLM_PROVIDER': 'gemini'
    }
    
    with patch('src.utils.config.SecureConfig.get') as mock_get, \
         patch('src.utils.config.SecureConfig.load') as mock_load:
        
        # Mock the load method to return a successful configuration
        mock_load.return_value = MagicMock()
        
        mock_get.side_effect = lambda var_name, default=None: mock_env_vars.get(var_name, default)
        
        return QuantumEthicalValidator()

def test_full_agent_pipeline(validator):
    code = "def example():\n  pass"
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
