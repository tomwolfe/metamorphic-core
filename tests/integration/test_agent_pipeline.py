import pytest
from unittest.mock import patch, MagicMock
from src.core.knowledge_graph import KnowledgeGraph
from src.core.ethics.governance import QuantumEthicalValidator

@pytest.fixture(scope="module")
def validator():
    # Mock environment variables
    mock_env_vars = {
        'GEMINI_API_KEY': 'test_gemini_key',
        'YOUR_GITHUB_API_KEY': 'test_github_key',
        'HUGGING_FACE_API_KEY': 'test_hf_key',
        'ZAP_API_KEY': 'test_zap_key',
        'LLM_PROVIDER': 'gemini'
    }
    
    mock_kg = MagicMock()
    mock_kg.search.return_value = [MagicMock(type="code_review")]

    with patch('src.utils.config.SecureConfig.get') as mock_get, \
         patch('src.utils.config.SecureConfig.load') as mock_load, \
         patch('src.core.knowledge_graph.KnowledgeGraph') as mock_kg_cls:
        
        mock_load.return_value = MagicMock()
        mock_get.side_effect = lambda var_name, default=None: mock_env_vars.get(var_name, default)
        mock_kg_cls.return_value = mock_kg
        
        return QuantumEthicalValidator()

def test_full_agent_pipeline(validator):
    code = "def example():\n  pass"
    result = validator.validate_code(code)
    
    # Assert the result contains necessary keys
    assert 'spec_analysis' in result
    assert 'security_scan' in result
    assert 'code_review' in result
    assert 'generated_tests' in result

    # Test KnowledgeGraph interaction using the mocked instance
    kg = KnowledgeGraph()
    nodes = kg.search("code_review")
    assert any(n.type == "code_review" for n in nodes)

    # Test score calculation
    assert 0.0 <= result.get('score', 0.0) <= 1.0
    if result['score'] < 0.7:
        assert result['status'] == "rejected"
    else:
        assert result['status'] == "approved"
