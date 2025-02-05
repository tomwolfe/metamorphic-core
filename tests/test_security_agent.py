# tests/test_security_agent.py
import pytest
import json
import os
from unittest.mock import patch, MagicMock
from src.core.agents.security_agent import SecurityAgent
from src.core.knowledge_graph import KnowledgeGraph
from src.utils.config import ConfigError

def testsanitization():
    agent = SecurityAgent()
    assert agent.sanitize_input("Test@123") == "Test123"
    assert agent.sanitize_input("<script>alert()</script>") == "scriptalertscript"
    assert agent.sanitize_input(None) is None
    assert agent.sanitize_input("Special chars: !@#$%^&*()_+=-`~[]{}|;':\",./<>?") == "Special chars: !_-;:,.?"
    long_input = "A" * 2000
    assert len(agent.sanitize_input(long_input)) == 1000

def test_env_validation_valid():
    with patch.dict('os.environ', {
        'GEMINI_API_KEY': 'AIzaSyxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'YOUR_GITHUB_API_KEY': 'ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'HUGGING_FACE_API_KEY': 'hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
    }):
        agent = SecurityAgent()
        assert agent._validate_environment() == True

def test_env_validation_invalid_gemini():
    with patch.dict('os.environ', {'GEMINI_API_KEY': 'invalid', 'YOUR_GITHUB_API_KEY': 'ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx', 'HUGGING_FACE_API_KEY': 'hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'}):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)

def test_env_validation_invalid_github():
    with patch.dict('os.environ', {'YOUR_GITHUB_API_KEY': 'invalid', 'GEMINI_API_KEY': 'AIzaSyxxxxxxxxxxxxxxxxxxxxxxxxxxxxx', 'HUGGING_FACE_API_KEY': 'hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'}):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for YOUR_GITHUB_API_KEY" in str(excinfo.value)

def test_env_validation_invalid_hf():
    with patch.dict('os.environ', {'HUGGING_FACE_API_KEY': 'invalid', 'GEMINI_API_KEY': 'AIzaSyxxxxxxxxxxxxxxxxxxxxxxxxxxxxx', 'YOUR_GITHUB_API_KEY': 'ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'}):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for HUGGING_FACE_API_KEY" in str(excinfo.value)

def test_env_validation_missing_vars():
    with patch.dict('os.environ', {}, clear=True):
        with pytest.raises(ConfigError) as excinfo:
            SecurityAgent()
        assert "Missing required environment variable" in str(excinfo.value)

def test_env_validation_example_keys():
    with patch.dict('os.environ', {
        'GEMINI_API_KEY': 'your_key_here',
        'YOUR_GITHUB_API_KEY': 'your_github_token',
        'HUGGING_FACE_API_KEY': 'your_hf_api_key'
    }):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)

def test_run_zap_baseline_scan():
    """Test ZAP baseline scan processing"""
    zap_report = {
        "alerts": [
            {
                "name": "SQL Injection",
                "riskcode": 3,
                "desc": "SQL injection vulnerability detected.",
                "solution": "Sanitize input parameters.",
                "reference": "https://example.com/sql-injection"
            },
            {
                "name": "Cross-Site Scripting",
                "riskcode": 2,
                "desc": "XSS vulnerability detected.",
                "solution": "Implement input validation.",
                "reference": "https://example.com/xss"
            }
        ]
    }

    kg_mock = MagicMock(spec=KnowledgeGraph)
    security_agent = SecurityAgent()
    security_agent.kg = kg_mock

    security_agent.run_zap_baseline_scan(
        target_url="http://localhost:5000/generate",
        findings=zap_report
    )

    assert kg_mock.add_security_finding.call_count == 2
    assert "SQL Injection" in str(kg_mock.add_security_finding.call_args_list[0])
    assert "Cross-Site Scripting" in str(kg_mock.add_security_finding.call_args_list[1])
