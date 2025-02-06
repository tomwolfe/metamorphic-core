# tests/test_llm_orchestration.py
import pytest
from unittest.mock import patch, MagicMock
from src.core.llm_orchestration import (
    LLMOrchestrator,
    LLMProvider,
    format_math_prompt,
    extract_boxed_answer
)
from src.utils.config import ConfigError
import google.genai  # Import genai here

def test_math_prompt_formatting():
    formatted = format_math_prompt("2+2")
    assert r"\boxed{}" in formatted
    assert "Question: 2+2" in formatted

def test_answer_extraction():
    assert extract_boxed_answer(r"Answer: \boxed{4}") == "4"
    assert extract_boxed_answer("No box here") == "No box here"

@patch('src.utils.config.SecureConfig.get')
def test_gemini_configuration(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'gemini',
        'GEMINI_API_KEY': 'test_key'
    }.get(var_name, default)
    orchestrator = LLMOrchestrator()
    assert orchestrator.config.provider == LLMProvider.GEMINI
    assert orchestrator.config.gemini_api_key == 'test_key'
    assert isinstance(orchestrator.client, google.genai.Client)
    assert orchestrator.client.model == 'gemini-2.0-flash-exp'  # Updated to gemini-2.0-flash-exp

@patch('src.utils.config.SecureConfig.get')
def test_hf_configuration(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'huggingface',
        'HUGGING_FACE_API_KEY': 'test_key'
    }.get(var_name, default)
    orchestrator = LLMOrchestrator()
    assert orchestrator.config.provider == LLMProvider.HUGGING_FACE
    assert orchestrator.config.hf_api_key == 'test_key'

@patch('src.utils.config.SecureConfig.get')
def test_missing_api_keys(mock_get):
    with pytest.raises(RuntimeError):
        with patch('src.utils.config.SecureConfig.get') as mock_get:
            mock_get.side_effect = lambda var_name, default=None: {
                'LLM_PROVIDER': 'gemini'
            }.get(var_name, default)
            LLMOrchestrator()

    with pytest.raises(RuntimeError):
        with patch('src.utils.config.SecureConfig.get') as mock_get:
            mock_get.side_effect = lambda var_name, default=None: {
                'LLM_PROVIDER': 'huggingface'
            }.get(var_name, default)
            LLMOrchestrator()

@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_gemini_generation(mock_get, mock_client):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'gemini',
        'GEMINI_API_KEY': 'test_key'
    }.get(var_name, default)
    mock_instance = mock_client.return_value
    mock_instance.models.generate_content.return_value = MagicMock(
        candidates=[MagicMock(
            content=MagicMock(
                parts=[MagicMock(text="Test response")]
            )
        )]
    )

    with patch('src.utils.config.SecureConfig.get'): # Just to satisfy context manager, not needed
        # config is already mocked by mock_get
        orchestrator = LLMOrchestrator()
        response = orchestrator.generate("test")
        assert "Test response" in response

@patch('huggingface_hub.InferenceClient.text_generation')
@patch('src.utils.config.SecureConfig.get')
def test_hf_generation(mock_get, mock_generate):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'huggingface',
        'HUGGING_FACE_API_KEY': 'test_key'
    }.get(var_name, default)
    mock_generate.return_value = "Test response"
    with patch('src.utils.config.SecureConfig.get'): # Just to satisfy context manager, not needed
        orchestrator = LLMOrchestrator()
        response = orchestrator.generate("test")
        assert response == "Test response"

def test_invalid_provider():
    with pytest.raises(ValueError):
        with patch('src.utils.config.SecureConfig.get') as mock_get:
            mock_get.side_effect = lambda var_name, default=None: {
                'LLM_PROVIDER': 'invalid'
            }.get(var_name, default)
            LLMOrchestrator()

@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_retry_logic(mock_get, mock_client):
    mock_instance = mock_client.return_value
    mock_get.side_effect = lambda var_name, default=None: {'GEMINI_API_KEY': 'test_key', 'LLM_PROVIDER': 'gemini'}.get(var_name, None)
    mock_instance.models.generate_content.side_effect = [Exception("API error"), Exception("API error"), Exception("API error")]

    with patch('src.utils.config.SecureConfig.get'): # Just to satisfy context manager, not needed
        with pytest.raises(RuntimeError):
            orchestrator = LLMOrchestrator()
            response = orchestrator.generate("test")

    assert mock_instance.models.generate_content.call_count == 3

def test_gemini_client_initialization():
    with patch('src.utils.config.SecureConfig.get') as mock_get:
        mock_get.side_effect = lambda var_name, default=None: {
            'LLM_PROVIDER': 'gemini', 'GEMINI_API_KEY': 'test_key'
        }.get(var_name, default)
        orchestrator = LLMOrchestrator()
        assert isinstance(orchestrator.client, google.genai.Client)
        assert orchestrator.client.api_key == 'test_key'  # Ensure api_key is accessible
        assert orchestrator.client.model == 'gemini-2.0-flash-exp'  # Updated to gemini-2.0-flash-exp
