# tests/integration/test_agent_pipeline.py
import pytest
from src.core.ethics.governance import QuantumEthicalValidator
from src.core.knowledge_graph import KnowledgeGraph

@pytest.fixture(scope="module")
def validator(monkeypatch):
    # Set dummy environment variables for testing
    monkeypatch.setenv("GEMINI_API_KEY", "test_gemini_key")
    monkeypatch.setenv("YOUR_GITHUB_API_KEY", "test_github_key")
    monkeypatch.setenv("HUGGING_FACE_API_KEY", "test_hf_key")
    monkeypatch.setenv("ZAP_API_KEY", "test_zap_key")  # Add ZAP_API_KEY too, just in case

    return QuantumEthicalValidator()

def test_full_agent_pipeline(validator):
    # This test will now run because the validator fixture
    # sets the necessary environment variables
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
