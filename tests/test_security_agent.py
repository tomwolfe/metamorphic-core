import pytest
import json
import os
from unittest.mock import patch, MagicMock
from src.core.agents.security_agent import SecurityAgent
from src.utils.config import SecureConfig, ConfigError
import logging

def setup_module():
    logging.basicConfig(level=logging.INFO)

def testsanitization():
    agent = SecurityAgent()
    assert agent.sanitize_input("Test@123") == "Test123"
    assert agent.sanitize_input("<script>alert()</script>") == "scriptalertscript"
    assert agent.sanitize_input(None) is None
    assert agent.sanitize_input("Special chars: !@#$%^&*()_+=-`~[]{}|;':\",./<>?") == "Special chars: !_-;:,.?"
    long_input = "A" * 2000
    assert len(agent.sanitize_input(long_input)) == 1000

@patch('src.utils.config.SecureConfig.get')
def test_env_validation_valid(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'GEMINI_API_KEY': 'AIzaSyxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'YOUR_GITHUB_API_KEY': 'ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'HUGGING_FACE_API_KEY': 'hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
    }.get(var_name, default)
    agent = SecurityAgent()
    assert agent._validate_environment() == True

@patch('src.utils.config.SecureConfig.get')
def test_env_validation_invalid_gemini(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'GEMINI_API_KEY': 'invalid',
        'YOUR_GITHUB_API_KEY': 'ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'HUGGING_FACE_API_KEY': 'hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
    }.get(var_name, default)
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)

@patch('src.utils.config.SecureConfig.get')
def test_env_validation_invalid_github(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'YOUR_GITHUB_API_KEY': 'invalid',
        'GEMINI_API_KEY': 'AIzaSyxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'HUGGING_FACE_API_KEY': 'hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
    }.get(var_name, default)
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid configuration for YOUR_GITHUB_API_KEY" in str(excinfo.value)

@patch('src.utils.config.SecureConfig.get')
def test_env_validation_invalid_hf(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'HUGGING_FACE_API_KEY': 'invalid',
        'GEMINI_API_KEY': 'AIzaSyxxxxxxxxxxxxxxxxxxxxxxxxxxxxx',
        'YOUR_GITHUB_API_KEY': 'ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
    }.get(var_name, default)
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid configuration for HUGGING_FACE_API_KEY" in str(excinfo.value)

@patch('src.utils.config.SecureConfig.get')
def test_env_validation_missing_vars(mock_get):
    mock_get.return_value = None
    with pytest.raises(ConfigError) as excinfo:
        SecurityAgent()
    assert "Missing required environment variable" in str(excinfo.value)

@patch('src.utils.config.SecureConfig.get')
def test_env_validation_example_keys(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'GEMINI_API_KEY': 'your_key_here',
        'YOUR_GITHUB_API_KEY': 'your_github_token',
        'HUGGING_FACE_API_KEY': 'yourhfaipkey'
    }.get(var_name, default)
    with pytest.raises(ValueError) as excinfo:
        SecurityAgent()
    assert "Invalid configuration for GEMINI_API_KEY" in str(excinfo.value)

@patch('src.core.agents.security_agent.ZAPv2')
@patch('src.utils.config.SecureConfig.get')
def test_run_zap_baseline_scan(mock_get, mock_zap):
    mock_get.return_value = 'test_zap_key'
    mock_instance = mock_zap.return_value
    mock_instance.ascan.scan.return_value = 'scan-id'
    mock_instance.ascan.status.return_value = 100
    mock_instance.core.alerts.return_value = []

    agent = SecurityAgent()
    results = agent.run_zap_baseline_scan("http://localhost")
    assert isinstance(results, list)
