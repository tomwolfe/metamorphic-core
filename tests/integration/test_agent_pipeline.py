import pytest
from unittest.mock import patch, MagicMock
import subprocess
from src.core.knowledge_graph import KnowledgeGraph
from src.core.ethics.governance import QuantumEthicalValidator
import os
from os import environ

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

    with (
        patch('src.core.agents.security_agent.SecurityAgent.run_zap_baseline_scan') as mock_zap,
        patch('src.core.agents.test_generator.TestGenAgent.generate_tests') as mock_tests,
        patch('subprocess.run') as mock_subprocess_run,
        patch.dict(os.environ, valid_mocks),
        patch('src.utils.config.SecureConfig.get', lambda *args, **kwargs: valid_mocks.get(args[0]) if args else None)
    ):

        mock_zap.return_value = {'alerts': [], 'scan_id': 'test_scan'}
        mock_tests.return_value = "def test_example(): pass"

        # Allow actual subprocess execution for analysis tools
        real_subprocess = subprocess.run
        def mock_subprocess(*args, **kwargs):
            if 'flake8' in args[0] or 'bandit' in args[0]:
                return real_subprocess(*args, **kwargs)
            else:
                return MagicMock(returncode=0)

        mock_subprocess_run side_effect = mock_subprocess

        # Initialize KnowledgeGraph once
        kg = KnowledgeGraph()
        validator = QuantumEthicalValidator()
        validator.spec_analyzer.kg = kg
        validator.code_review_agent.kg = kg

        yield validator

def test_full_agent_pipeline(validator):
    # Use code that triggers findings
    code = "def example(x): return eval(x)"  # Triggers bandit security warning

    # Run the validation pipeline
    result = validator.validate_code(code)

    # Access the shared KnowledgeGraph
    kg = validator.code_review_agent.kg
    nodes = kg.search("code_review")

    # Assertion to check for code_review nodes
    assert any(n.type == "code_review" for n in nodes), "No code_review nodes found in the KnowledgeGraph"
