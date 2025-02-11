import pytest
from unittest.mock import patch, MagicMock
from src.core.knowledge_graph import KnowledgeGraph
from src.core.ethics.governance import QuantumEthicalValidator

@pytest.fixture(scope="module")
def validator():
    """Fixture with valid mock credentials passing SecureConfig checks"""
    valid_mocks = {
        'GEMINI_API_KEY': 'AIzaSy' + 'a'*35,
        'YOUR_GITHUB_API_KEY': 'ghp_' + 'b'*36,
        'HUGGING_FACE_API_KEY': 'hf_' + 'c'*31,
        'ZAP_API_KEY': 'zap_' + 'd'*36,
        'LLM_PROVIDER': 'gemini',
        'LLM_MAX_RETRIES': '3',
        'LLM_TIMEOUT': '30'
    }

    with patch('src.core.agents.security_agent.SecurityAgent.run_zap_baseline_scan') as mock_zap, \
         patch('src.core.agents.test_generator.TestGenAgent.generate_tests') as mock_tests, \
         patch.dict(os.environ, valid_mocks), \
         patch('src.utils.config.SecureConfig.get', lambda x, y: valid_mocks.get(x, y)):  # Fixed lambda to accept two arguments

        mock_zap.return_value = {'alerts': [], 'scan_id': 'test_scan'}
        mock_tests.return_value = "def test_example(): pass"

        yield QuantumEthicalValidator()
             
def test_full_agent_pipeline(validator):
    code = "def example():\n  pass"
    result = validator.validate_code(code)
    
    assert 'spec_analysis' in result
    assert 'security_scan' in result
    assert 'code_review' in result
    assert 'generated_tests' in result
    
    # Test KnowledgeGraph interaction
    kg = KnowledgeGraph()  # This will use the mocked instance from the fixture
    nodes = kg.search("code_review")
    assert any(n.type == "code_review" for n in nodes)
    
    # Test score calculation
    assert 0 <= result['score'] <= 1
    if result['score'] < 0.7:
        assert result['status'] == "rejected"
    else:
        assert result['status'] == "approved"
