import pytest
from unittest.mock import patch, MagicMock
from src.core.llm_orchestration import (
    LLMOrchestrator,
    format_math_prompt,
    extract_boxed_answer
)

def test_math_prompt_formatting():
    formatted = format_math_prompt("2+2")
    assert r"\boxed{}" in formatted
    assert "step by step" in formatted
    assert "Question: 2+2" in formatted

def test_answer_extraction():
    assert extract_boxed_answer(r"Answer: \boxed{4}") == "4"
    assert extract_boxed_answer("No box here") == "No box here"

@patch('huggingface_hub.InferenceClient.text_generation')
def test_hf_generation_params(mock_generate):
    mock_generate.return_value = "Test response"
    orchestrator = LLMOrchestrator()
    orchestrator._configure_providers()
    
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
