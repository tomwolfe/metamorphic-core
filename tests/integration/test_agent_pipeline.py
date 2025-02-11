import pytest
from unittest.mock import patch, MagicMock
from src.core.knowledge_graph import KnowledgeGraph
from src.core.ethics.governance import QuantumEthicalValidator
import os
from os import environ

@pytest.fixture(scope="module")
def validator():
    valid_mocks = {
        'GEMINI_API_KEY': 'AIzaSy' + 'a'*35,
        'YOUR_GITHUB_API_KEY': 'ghp_' + 'b'*36,
        'HUGGING_FACE_API_KEY': 'hf_' + 'c'*31,
        'ZAP_API_KEY': 'zap_' + 'd'*36,
        'LLM_PROVIDER': 'gemini',
        'LLM_MAX_RETRIES': '3',
        'LLM_TIMEOUT': '30'
    }

    with (
        patch('src.core.agents.security_agent.SecurityAgent.run_zap_baseline_scan') as mock_zap,
        patch('src.core.agents.test_generator.TestGenAgent.generate_tests') as mock_tests,
        patch('subprocess.run') as mock_subprocess_run,
        patch.dict(os.environ, valid_mocks),
        patch('src.utils.config.SecureConfig.get', lambda *args, **kwargs: valid_mocks.get(args[0]) if args else None)
    ):

        mock_zap.return_value = {'alerts': [], 'scan_id': 'test_scan'}
        mock_tests.return_value = "def test_example(): pass"
        mock_subprocess_run.side_effect = lambda *args, **kwargs: (
            MagicMock(returncode=0, stdout="", stderr="") if 'flake8' in args[0]
            else MagicMock(returncode=0, stdout='{"results": []}', stderr="")
        )

        yield QuantumEthicalValidator()

def test_full_agent_pipeline(validator):
    # Use code that triggers findings
    code = "def example(x):\n    return eval(x)"  # Triggers bandit security warning

    # Remove mocks temporarily to allow real analysis
    with patch('subprocess.run') as mock_subprocess:
        mock_subprocess.side_effect = lambda *args, **kwargs: (
            MagicMock(returncode=0, stdout="", stderr="") if 'flake8' in args[0]
            else MagicMock(returncode=0, stdout='{"results": [{"test_id": "B601", "issue_severity": "HIGH", "filename": "test.py", "line_number": 1}]}', stderr="")
        )

        result = validator.validate_code(code)

    agent = validator.code_review_agent
    kg = agent.kg
    nodes = kg.search("code_review")
    assert any(n.type == "code_review" for n in nodes)
