import pytest
from unittest.mock import patch, MagicMock
from src.core.ethics.governance import QuantumEthicalValidator

@pytest.fixture(scope="module")
def validator():
    # Mock environment variables with valid patterns for all required keys
    mock_env_vars = {
        'GEMINI_API_KEY': 'AIzaSyA1234567890ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz',  # Gemini API key must start with 'AIzaSy' followed by 32 characters
        'YOUR_GITHUB_API_KEY': 'ghp_abcdefghijklmnopqrstuvwxyz123456',  # GitHub API key must be 40 characters long
        'HUGGING_FACE_API_KEY': 'hf_abcdefghijklmnopqrstuvwxyz123456',  # Hugging Face API key starts with 'hf_'
        'ZAP_API_KEY': 'test_zap_key',
        'LLM_PROVIDER': 'gemini'
    }
    
    with patch('src.utils.config.SecureConfig.get') as mock_get, \
         patch('src.utils.config.SecureConfig.load') as mock_load, \
         patch('google.genai.Client', autospec=True) as mock_genai_client:
        
        # Mock the load method to bypass actual loading
        mock_load.return_value = MagicMock()
        
        # Ensure get method returns mocked variables
        mock_get.side_effect = lambda var_name, default=None: mock_env_vars.get(var_name, default)
        
        # Configure Gemini client mock to avoid real API calls
        mock_genai_client.return_value.models.generate_content.return_value.candidates = [
            MagicMock(content=MagicMock(parts=[MagicMock(text='test_response')]))
        ]
        
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
