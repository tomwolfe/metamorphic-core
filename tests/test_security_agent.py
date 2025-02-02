import pytest
import os
from src.core.agents.security_agent import SecurityAgent
from unittest.mock import patch

def test_sanitization():
    agent = SecurityAgent()
    assert agent.sanitize_input("Test@123") == "Test123"
    assert agent.sanitize_input("<script>alert()</script>") == "scriptalertscript"
    assert agent.sanitize_input(None) is None
    # Expected output now reflects the original order of allowed characters
    assert agent.sanitize_input("Special chars: !@#$%^&*()_+=-`~[]{}|;':\",./<>?") == "Special chars: !_ -;:,.?"
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
    with patch.dict('os.environ', {'GEMINI_API_KEY': 'invalid'}):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)

def test_env_validation_invalid_github():
    with patch.dict('os.environ', {'YOUR_GITHUB_API_KEY': 'invalid'}):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for YOUR_GITHUB_API_KEY" in str(excinfo.value)

def test_env_validation_invalid_hf():
    with patch.dict('os.environ', {'HUGGING_FACE_API_KEY': 'invalid'}):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for HUGGING_FACE_API_KEY" in str(excinfo.value)

def test_env_validation_missing_vars():
    with patch.dict('os.environ', {}):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)

def test_env_validation_example_keys():
    with patch.dict('os.environ', {
        'GEMINI_API_KEY': 'your_key_here',
        'YOUR_GITHUB_API_KEY': 'your_github_token',
        'HUGGING_FACE_API_KEY': 'your_hf_api_key'
    }):
        with pytest.raises(ValueError) as excinfo:
            SecurityAgent()
        assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)
