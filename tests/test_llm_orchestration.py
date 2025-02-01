# tests/test_llm_orchestration.py
import pytest
from unittest.mock import patch, MagicMock
from src.core.llm_orchestration import (
    LLMOrchestrator,
    LLMProvider,
    format_math_prompt,
    extract_boxed_answer
)

def test_math_prompt_formatting():
    formatted = format_math_prompt("2+2")
    # Check for properly escaped LaTeX using raw string in assert
    assert r"\boxed{}" in formatted
    assert "step by step" in formatted
    assert "Question: 2+2" in formatted
    assert "Answer:" in formatted

def test_answer_extraction():
    assert extract_boxed_answer(r"Answer: \boxed{4}") == "4"
    assert extract_boxed_answer("No box here") == "No box here"

@patch('google.genai.GenerativeModel.generate_content')
def test_hf_generation_params(mock_generate):
    mock_generate.return_value = "Test response"
    orchestrator = LLMOrchestrator()
    # No need to call orchestrator._configure_providers() directly here

    # Use patch.dict to ensure Hugging Face provider is active for this test
    with patch.dict('os.environ', {'LLM_PROVIDER': 'huggingface'}):
        orchestrator._configure_providers() # Configure providers within the patched env
        if orchestrator.active_provider == LLMProvider.HUGGING_FACE:
            orchestrator.generate("test")
            mock_generate.assert_called_with(
                "test",
                max_new_tokens=2048,
                temperature=0.6,
                top_p=0.95,
                repetition_penalty=1.2,
                do_sample=True,
                seed=42,
                stop_sequences=["</s>"],
                return_full_text=False
            )

@patch('google.genai.GenerativeModel.generate_content')
def test_gemini_thinking_model(mock_generate_content):
    mock_generate_content.return_value = MagicMock(
        candidates=[MagicMock(
            content=MagicMock(
                parts=[
                    MagicMock(text="Model Thought: Thinking process...", thought=True),
                    MagicMock(text="Model Response: Final answer.", thought=False)
                ]
            )
        )]
    )
    orchestrator = LLMOrchestrator()
    with patch.dict('os.environ', {'LLM_PROVIDER': 'gemini'}):
        orchestrator._configure_providers()
        response = orchestrator.generate("test question")
        assert "Model Thought:" in response
        assert "Model Response:" in response
        mock_generate_content.assert_called_once() # Verify mock is called
@patch('huggingface_hub.InferenceClient.text_generation')
def test_deepseek_generation(mock_hf_generate):
    mock_hf_generate.return_value = "DeepSeek Test Response"
    orchestrator = LLMOrchestrator()
    with patch.dict('os.environ', {'LLM_PROVIDER': 'huggingface'}):
        orchestrator._configure_providers()
        response = orchestrator.generate("test prompt")
        assert response == "DeepSeek Test Response"
        mock_hf_generate.assert_called_once()
