# tests/integration/test_agent_pipeline.py
import pytest
from src.core.ethics.governance import QuantumEthicalValidator

@pytest.fixture(scope="module")
def validator():
    """Fixture to provide a QuantumEthicalValidator with mocked environment variables."""
    with patch('src.utils.config.SecureConfig') as mock_secure_config:
        # Mock the get method to return predefined values
        mock_secure_config.get.side_effect = lambda var_name, default=None: {
            'GEMINI_API_KEY': 'test_gemini_key',
            'YOUR_GITHUB_API_KEY': 'test_github_key',
            'HUGGING_FACE_API_KEY': 'test_hf_key',
            'ZAP_API_KEY': 'test_zap_key',
            # Add any other required environment variables here
            # For example:
            'LLM_PROVIDER': 'gemini',
            'LLM_MAX_RETRIES': '3',
            'LLM_TIMEOUT': '30'
        }.get(var_name, default)
        
        # Mock the load method to prevent actual environment checks
        mock_secure_config.load.return_value = None
        
        return QuantumEthicalValidator()


def test_full_agent_pipeline():
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
