import pytest
from unittest.mock import patch, MagicMock
from src.core.ethics.governance import QuantumEthicalValidator

@pytest.fixture(scope="module")
def validator():
    with patch('src.utils.config.SecureConfig.get') as mock_get:
        with patch('src.utils.config.SecureConfig.load') as mock_load:
            # Mock the load method to not perform any checks
            mock_load.return_value = MagicMock()
            mock_get.side_effect = lambda var_name, default=None: {
                'GEMINI_API_KEY': 'test_gemini_key',
                'YOUR_GITHUB_API_KEY': 'test_github_key',
                'HUGGING_FACE_API_KEY': 'test_hf_key',
                'ZAP_API_KEY': 'test_zap_key'
            }.get(var_name, default)
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
