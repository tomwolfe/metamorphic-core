import pytest
from unittest.mock import patch, MagicMock
from src.core.llm_orchestration import (
    LLMOrchestrator,
    LLMProvider,
    format_math_prompt,
    extract_boxed_answer
)
from src.utils.config import ConfigError

def test_math_prompt_formatting():
    formatted = format_math_prompt("2+2")
    assert r"\boxed{}" in formatted
    assert "Question: 2+2" in formatted

def test_answer_extraction():
    assert extract_boxed_answer(r"Answer: \boxed{4}") == "4"
    assert extract_boxed_answer("No box here") == "No box here"

@patch.dict('os.environ', {'LLM_PROVIDER': 'gemini', 'GEMINI_API_KEY': 'test_key'})
def test_gemini_configuration():
    orchestrator = LLMOrchestrator()
    assert orchestrator.config.provider == LLMProvider.GEMINI
    assert orchestrator.config.gemini_api_key == 'test_key'
    assert isinstance(orchestrator.client, genai.Client)
    assert orchestrator.client.model == 'gemini-2.0-flash-exp'  # Updated to gemini-2.0-flash-exp

@patch.dict('os.environ', {'LLM_PROVIDER': 'huggingface', 'HUGGING_FACE_API_KEY': 'test_key'})
def test_hf_configuration():
    orchestrator = LLMOrchestrator()
    assert orchestrator.config.provider == LLMProvider.HUGGING_FACE
    assert orchestrator.config.hf_api_key == 'test_key'

def test_missing_api_keys():
    with pytest.raises(RuntimeError):
        with patch.dict('os.environ', {'LLM_PROVIDER': 'gemini'}):
            LLMOrchestrator()
            
    with pytest.raises(RuntimeError):
        with patch.dict('os.environ', {'LLM_PROVIDER': 'huggingface'}):
            LLMOrchestrator()

@patch('google.genai.Client')
def test_gemini_generation(mock_client):
    mock_instance = mock_client.return_value
    mock_instance.models.generate_content.return_value = MagicMock(
        candidates=[MagicMock(
            content=MagicMock(
                parts=[MagicMock(text="Test response")]
            )
        )]
    )
    
    with patch.dict('os.environ', {'LLM_PROVIDER': 'gemini', 'GEMINI_API_KEY': 'test_key'}):
        orchestrator = LLMOrchestrator()
        response = orchestrator.generate("test")
        assert "Test response" in response

@patch('huggingface_hub.InferenceClient.text_generation')
def test_hf_generation(mock_generate):
    mock_generate.return_value = "Test response"
    with patch.dict('os.environ', {'LLM_PROVIDER': 'huggingface', 'HUGGING_FACE_API_KEY': 'test_key'}):
        orchestrator = LLMOrchestrator()
        response = orchestrator.generate("test")
        assert response == "Test response"

def test_invalid_provider():
    with pytest.raises(ValueError):
        with patch.dict('os.environ', {'LLM_PROVIDER': 'invalid'}):
            LLMOrchestrator()

@patch('google.genai.Client')
def test_retry_logic(mock_client):
    mock_instance = mock_client.return_value
    mock_instance.models.generate_content.side_effect = [Exception("API error"), Exception("API error"), Exception("API error")]
    
    with patch.dict('os.environ', {'LLM_PROVIDER': 'gemini', 'GEMINI_API_KEY': 'test_key'}):
        with pytest.raises(RuntimeError):
            orchestrator = LLMOrchestrator()
            orchestrator.generate("test")
            
    assert mock_instance.models.generate_content.call_count == 3

def test_gemini_client_initialization():
    with patch.dict('os.environ', {'LLM_PROVIDER': 'gemini', 'GEMINI_API_KEY': 'test_key'}):
        orchestrator = LLMOrchestrator()
        assert isinstance(orchestrator.client, genai.Client)
        assert orchestrator.client.api_key == 'test_key'
        assert orchestrator.client.model == 'gemini-2.0-flash-exp'  # Updated to gemini-2.0-flash-exp
