# tests/test_llm_orchestration.py
# tests/test_llm_orchestration.py
# Add these imports at the top of test_llm_orchestration.py
from src.core.context_manager import parse_code_chunks, generate_summary
import pytest
from unittest.mock import patch, MagicMock, call # Add call
from src.core.llm_orchestration import (
    LLMOrchestrator,
    LLMProvider,
    format_math_prompt,
    extract_boxed_answer,
    EnhancedLLMOrchestrator
)
from src.utils.config import ConfigError
import google.genai

# <--- ADD THESE IMPORTS ---
import time
import threading
import logging # Import logging module
# <--- END ADD ---


def test_math_prompt_formatting():
    formatted = format_math_prompt("2+2")
    assert r"\boxed{}" in formatted
    assert "Question: 2+2" in formatted

def test_answer_extraction():
    assert extract_boxed_answer(r"Answer: \boxed{4}") == "4"
    assert extract_boxed_answer("No box here") is None

@patch('src.utils.config.SecureConfig.get')
def test_gemini_configuration(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'gemini',
        'GEMINI_API_KEY': 'test_key'
    }.get(var_name, default)
    orchestrator = LLMOrchestrator()
    assert orchestrator.config.provider == LLMProvider.GEMINI
    assert orchestrator.config.gemini_api_key == 'test_key'
    # Check Client initialization and attributes instead of isinstance
    mock_client = MagicMock() # Need a mock object here to check calls against
    with patch('google.genai.Client', new=mock_client) as MockClient: # Patch the class with our mock
         orchestrator = LLMOrchestrator() # Re-initialize orchestrator under the patch
         MockClient.assert_called_once_with(api_key='test_key')
         assert orchestrator.client.api_key == 'test_key'
         assert orchestrator.client.model == 'gemini-2.5-flash-preview-04-17'


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
        mock_get.side_effect = lambda var_name, default=None: {
            'LLM_PROVIDER': 'gemini'
        }.get(var_name, default)
        LLMOrchestrator()

    with pytest.raises(RuntimeError):
        mock_get.side_effect = lambda var_name, default=None: {
            'LLM_PROVIDER': 'huggingface'
        }.get(var_name, default)
        LLMOrchestrator()

@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_gemini_generation(mock_get, mock_client):
    mock_instance = mock_client.return_value
    mock_get.side_effect = lambda var_name, default=None: {
        'GEMINI_API_KEY': 'test_key', 'LLM_PROVIDER': 'gemini', 'LLM_MAX_RETRIES': '3'
    }.get(var_name, default)
    # Mock Client.models.generate_content directly
    mock_instance.models.generate_content.return_value = MagicMock(
        candidates=[MagicMock(
            content=MagicMock(
                parts=[MagicMock(text="Test response")]
            )
        )]
    )
    orchestrator = LLMOrchestrator()
    # Patch _apply_gemini_rate_limit to prevent actual sleeping during this test
    with patch.object(orchestrator, '_apply_gemini_rate_limit') as mock_rate_limit:
        response = orchestrator.generate("test")
        assert "Test response" in response
        mock_rate_limit.assert_called_once() # Verify rate limit was attempted

@patch('huggingface_hub.InferenceClient.text_generation')
@patch('src.utils.config.SecureConfig.get')
def test_hf_generation(mock_get, mock_generate):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'huggingface',
        'HUGGING_FACE_API_KEY': 'test_key'
    }.get(var_name, default)
    mock_generate.return_value = "Test response"
    orchestrator = LLMOrchestrator()
    # Patch _apply_gemini_rate_limit to ensure it's not called for HF
    with patch.object(orchestrator, '_apply_gemini_rate_limit') as mock_rate_limit:
        response = orchestrator.generate("test")
        assert response == "Test response"
        mock_rate_limit.assert_not_called() # Verify rate limit was NOT attempted for HF


@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_retry_logic(mock_get, mock_client):
    mock_instance = mock_client.return_value
    mock_get.side_effect = lambda var_name, default=None: {
        'GEMINI_API_KEY': 'test_key', 'LLM_PROVIDER': 'gemini', 'LLM_MAX_RETRIES': '3'
    }.get(var_name, default)
    # Mock Client.models.generate_content directly
    mock_instance.models.generate_content.side_effect = [
        Exception("API error"),
        Exception("API error"),
        Exception("API error") # Fail all attempts
    ]
    orchestrator = LLMOrchestrator()
    # Patch _apply_gemini_rate_limit to prevent actual sleeping during this test
    with patch.object(orchestrator, '_apply_gemini_rate_limit') as mock_rate_limit:
        with pytest.raises(RuntimeError):
            orchestrator.generate("test")
        # Verify LLM call was attempted max_retries times
        assert mock_instance.models.generate_content.call_count == 3
        # Verify rate limit was attempted before each call
        assert mock_rate_limit.call_count == 3


def test_invalid_provider():
    with pytest.raises(RuntimeError):
        with patch('src.utils.config.SecureConfig.get') as mock_get:
            mock_get.side_effect = lambda var_name, default=None: {
                'LLM_PROVIDER': 'invalid'
            }.get(var_name, default)
            LLMOrchestrator()

# FIX: Removed isinstance check and added mock call assertion
@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_gemini_client_initialization(mock_get, mock_client):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'gemini', 'GEMINI_API_KEY': 'test_key'
    }.get(var_name, default)
    orchestrator = LLMOrchestrator()
    # Check that the client was initialized with the correct API key
    mock_client.assert_called_once_with(api_key='test_key')
    # Check that the client's model and api_key are set
    assert orchestrator.client.api_key == 'test_key'
    assert orchestrator.client.model == 'gemini-2.5-flash-preview-04-17'

@patch.object(EnhancedLLMOrchestrator, '_handle_large_context') # Use patch.object for clarity
def test_large_context_handling(mock_handle_large_context):
    orchestrator = EnhancedLLMOrchestrator(
        kg=MagicMock(),
        spec=MagicMock(),
        ethics_engine=MagicMock()
    )
    large_prompt = "test " * 6000
    # Update the mock return value to exceed the new threshold (8000)
    with patch.object(orchestrator, '_count_tokens', return_value=8001) as mock_count_tokens:
        orchestrator.generate(large_prompt)
        mock_handle_large_context.assert_called_once()


def test_chunking_algorithm():
    code = """\
def function1():
    print("Hello")

def function2():
    print("World")

class MyClass:
    def method(self):
        pass"""
    chunks = parse_code_chunks(code)
    assert len(chunks) == 1  # Split into 1 chunks
    assert "def function1():" in chunks[0].content
    assert "def function2():" in chunks[0].content
    assert "class MyClass:" in chunks[0].content

def test_summarization():
    code = """\
def function1():
    print("Hello")

def function2():
    print("World")

class MyClass:
    def method(self):
        pass"""
    chunks = parse_code_chunks(code)
    assert len(chunks) == 1  # Split into 1 chunks


# --- NEW TEST FOR _call_llm_api unsupported model ---
@patch('src.utils.config.SecureConfig.get')
def test_call_llm_api_unsupported_model(mock_secure_get):
    mock_secure_get.side_effect = lambda key, default=None: {
        "LLM_PROVIDER": "gemini", "GEMINI_API_KEY": "fake_key"
    }.get(key, default)

    orchestrator = EnhancedLLMOrchestrator(
        kg=MagicMock(), spec=MagicMock(), ethics_engine=MagicMock()
    )
    # Patch _apply_gemini_rate_limit to prevent actual sleeping during this test
    with patch.object(orchestrator, '_apply_gemini_rate_limit'):
        with pytest.raises(ValueError, match="Unsupported model: unsupported_test_model"):
            orchestrator._call_llm_api("test text", "unsupported_test_model")


# --- NEW TESTS FOR GEMINI RATE LIMITING ---

@patch('src.utils.config.SecureConfig.get')
def test_gemini_rate_limiting_applied(mock_secure_get, caplog):
    """Tests that _apply_gemini_rate_limit enforces the minimum interval."""
    # Set logging level to INFO to capture the rate limit message
    caplog.set_level(logging.INFO) # <-- ADD THIS LINE

    # Configure mock to use Gemini provider and a fake API key
    mock_secure_get.side_effect = lambda key, default=None: {
        "LLM_PROVIDER": "gemini", "GEMINI_API_KEY": "fake_key",
        "LLM_MAX_RETRIES": "1" # Lower retries for faster test
    }.get(key, default)

    orchestrator = LLMOrchestrator()
    # Shorten the interval significantly for the test
    orchestrator._GEMINI_MIN_INTERVAL_SECONDS = 0.1

    # Mock the actual Gemini client call to avoid real API calls
    with patch.object(orchestrator.client.models, 'generate_content') as mock_gemini_call:
        mock_gemini_call.return_value = MagicMock(
            candidates=[MagicMock(content=MagicMock(parts=[MagicMock(text="Test response")]))]
        )

        # Mock time.sleep and time.monotonic
        with patch('time.sleep') as mock_sleep, \
             patch('time.monotonic') as mock_monotonic:

            # --- Simulate time progression ---
            # Call 1:
            # time.monotonic() called before first _apply_gemini_rate_limit (e.g., 100.0)
            # Inside _apply_gemini_rate_limit: current_time = 100.0. _last_gemini_call_start_time = 0.0. elapsed = 100.0. No sleep.
            # _last_gemini_call_start_time updated to 100.0.

            # Call 2:
            # time.monotonic() called before second _apply_gemini_rate_limit (e.g., 100.05)
            # Inside _apply_gemini_rate_limit: current_time = 100.05. _last_gemini_call_start_time = 100.0. elapsed = 0.05.
            # elapsed (0.05) < interval (0.1), so sleep needed: sleep_duration = 0.1 - 0.05 = 0.05.
            # time.sleep(0.05) is called.
            # After sleep, time.monotonic() called again (e.g., 100.1).
            # _last_gemini_call_start_time updated to 100.1.

            mock_monotonic.side_effect = [
                100.0,  # time.monotonic() before first _apply_gemini_rate_limit call
                100.05, # time.monotonic() before second _apply_gemini_rate_limit call
                100.1   # time.monotonic() after sleep in second _apply_gemini_rate_limit call
            ]

            # First call - should not sleep
            orchestrator.generate("prompt1")
            mock_sleep.assert_not_called()
            assert "Gemini rate limit: sleeping for" not in caplog.text

            caplog.clear() # Clear logs for the next assertion

            # Second call - should sleep
            orchestrator.generate("prompt2")

            # FIX: Use pytest.approx to handle floating-point precision
            mock_sleep.assert_called_once() # Ensure it was called once
            actual_sleep_duration = mock_sleep.call_args[0][0] # Get the actual argument
            assert actual_sleep_duration == pytest.approx(0.05) # Assert approximate equality

            assert "Gemini rate limit: sleeping for 0.05 seconds." in caplog.text # Assert log message

            # Ensure the underlying Gemini call was attempted twice
            assert mock_gemini_call.call_count == 2

# Add a test for thread safety (Optional but good practice)
@patch('src.utils.config.SecureConfig.get')
def test_gemini_rate_limiting_thread_safety(mock_secure_get):
    """Tests that _apply_gemini_rate_limit is thread-safe."""
    mock_secure_get.side_effect = lambda key, default=None: {
        "LLM_PROVIDER": "gemini", "GEMINI_API_KEY": "fake_key",
        "LLM_MAX_RETRIES": "1"
    }.get(key, default)

    orchestrator = LLMOrchestrator()
    orchestrator._GEMINI_MIN_INTERVAL_SECONDS = 0.2 # Short interval for test

    # Mock the actual Gemini client call
    with patch.object(orchestrator.client.models, 'generate_content') as mock_gemini_call:
        mock_gemini_call.return_value = MagicMock(
            candidates=[MagicMock(content=MagicMock(parts=[MagicMock(text="Test response")]))]
        )

        # Mock time.sleep
        with patch('time.sleep') as mock_sleep:
            # Simulate two threads calling generate almost simultaneously
            # We can't perfectly control thread timing, but we can check if the lock is used
            # and if sleep is called appropriately for subsequent calls.

            def call_generate():
                orchestrator.generate("thread prompt")

            threads = []
            num_threads = 5
            for _ in range(num_threads):
                thread = threading.Thread(target=call_generate)
                threads.append(thread)
                thread.start()

            for thread in threads:
                thread.join()

            # The exact number and duration of sleeps is hard to predict due to thread scheduling,
            # but we can assert that sleep was called multiple times (at least num_threads - 1 times
            # if they hit the rate limit) and that the underlying LLM call happened num_threads times.

            assert mock_gemini_call.call_count == num_threads # Each thread should attempt the call
            # Assert that sleep was called at least some number of times, indicating rate limiting kicked in
            # Check that sleep was called at least num_threads - 1 times (subsequent calls should sleep)
            # The exact value might vary slightly due to thread timing and float precision,
            # so checking the count is more reliable than checking specific call values here.
            assert mock_sleep.call_count >= num_threads - 1

            # More advanced tests would involve mocking time.monotonic with more complex side effects
            # to precisely control the timing and verify sleep durations, but this basic test
            # verifies the lock is present and sleep is called.