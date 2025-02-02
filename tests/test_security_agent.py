import pytest
import os
from src.core.agents.security_agent import SecurityAgent
from src.utils.config import ConfigError

def test_sanitization():
    agent = SecurityAgent()
    assert agent.sanitize_input("Test@123") == "Test123"
    assert agent.sanitize_input("<script>alert()</script>") == "scriptalertscript"
    assert agent.sanitize_input(None) is None
    assert agent.sanitize_input("Special chars: !@#$%^&*()_+=-`~[]\{}|;':\",./<>?") == "Special chars: _-.,:;!?"
    long_input = "A" * 2000
    assert len(agent.sanitize_input(long_input)) == 1000

def test_env_validation_valid(mocker):
    mocker.patch.dict('os.environ', {
        'GEMINI_API_KEY': 'AIzaSyxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'YOUR_GITHUB_API_KEY': 'ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'HUGGING_FACE_API_KEY': 'hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
    })
    agent = SecurityAgent()
    assert agent._validate_environment() == True

def test_env_validation_invalid_gemini(mocker):
    mocker.patch.dict('os.environ', {'GEMINI_API_KEY': 'invalid'})
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid format for GEMINI_API_KEY" in str(excinfo.value)

def test_env_validation_invalid_github(mocker):
    mocker.patch.dict('os.environ', {'YOUR_GITHUB_API_KEY': 'invalid'})
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid format for YOUR_GITHUB_API_KEY" in str(excinfo.value)

def test_env_validation_invalid_hf(mocker):
    mocker.patch.dict('os.environ', {'HUGGING_FACE_API_KEY': 'invalid'})
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid format for HUGGING_FACE_API_KEY" in str(excinfo.value)

def test_env_validation_missing_vars(mocker):
    mocker.patch.dict('os.environ', {}) # No API keys set
    with pytest.raises(ConfigError) as excinfo:
        SecurityAgent()
    assert "Missing required environment variables" in str(excinfo.value)

def test_env_validation_example_keys(mocker):
    mocker.patch.dict('os.environ', {
        'GEMINI_API_KEY': 'your_key_here',
        'YOUR_GITHUB_API_KEY': 'your_github_token',
        'HUGGING_FACE_API_KEY': 'your_hf_api_key'
    })
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)
