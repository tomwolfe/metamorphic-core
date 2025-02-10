# tests/integration/test_agent_pipeline.py
import pytest
from src.core.ethics.governance import QuantumEthicalValidator
from src.core.knowledge_graph import KnowledgeGraph
from unittest.mock import patch

@pytest.fixture(scope="module")
def validator():
    # Use patch to mock SecureConfig.get directly
    with patch('src.utils.config.SecureConfig.get') as mock_config_get:
        mock_config_get.side_effect = lambda var_name, default=None: {
            'GEMINI_API_KEY': 'test_gemini_key',
            'YOUR_GITHUB_API_KEY': 'test_github_key',
            'HUGGING_FACE_API_KEY': 'test_hf_key',
            'ZAP_API_KEY': 'test_zap_key'
        }.get(var_name, default)
        return QuantumEthicalValidator()

def test_full_agent_pipeline(validator):
    code = "def example():\n  pass" # Added newline and indent to be valid code
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
