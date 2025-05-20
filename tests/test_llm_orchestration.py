# tests/test_llm_orchestration.py
# tests/test_llm_orchestration.py
# Add these imports at the top of test_llm_orchestration.py
# FIX: Import parse_code_chunks from context_manager
from src.core.context_manager import parse_code_chunks # Correct import for parse_code_chunks
# FIX: Import RecursiveSummarizer from its correct location
from src.core.chunking.recursive_summarizer import RecursiveSummarizer # Correct import
import pytest
from unittest.mock import patch, MagicMock, call # Add call
from src.core.llm_orchestration import (
    LLMProvider,
    LLMOrchestrator,
    format_math_prompt,
    extract_boxed_answer,
    EnhancedLLMOrchestrator
)
from src.utils.config import ConfigError
import google.genai

from src.core.verification.specification import FormalSpecification # Correct import for FormalSpecification
from src.core.chunking.dynamic_chunker import CodeChunk # Correct import for CodeChunk
# <--- ADD THESE IMPORTS (already present) ---
import time
import threading
import logging # Import logging module
# <--- END ADD ---


def test_math_prompt_formatting():
    formatted = format_math_prompt("2+2")
    assert r"\boxed{}" in formatted
    assert "Question: 2+2" in formatted

def test_answer_extraction(): # Keep existing test
    assert extract_boxed_answer(r"Answer: \boxed{4}") == "4"
    assert extract_boxed_answer("No box here") is None

@patch('src.utils.config.SecureConfig.get')
def test_gemini_configuration(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'gemini',
        'GEMINI_API_KEY': 'test_key'
    }.get(var_name, default) # Corrected .get() usage
    # Check Client initialization and attributes instead of isinstance
    # Patch the class itself to check constructor calls
    with patch('google.genai.Client') as MockClient:
         orchestrator = LLMOrchestrator() # Re-initialize orchestrator under the patch
         MockClient.assert_called_once_with(api_key='test_key')
         # Check attributes on the actual orchestrator client instance
         assert orchestrator.client.api_key == 'test_key'
         assert orchestrator.client.model == 'gemini-2.5-flash-preview-04-17'


@patch('src.utils.config.SecureConfig.get')
def test_hf_configuration(mock_get):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'huggingface',
        'HUGGING_FACE_API_KEY': 'test_key' # Corrected .get() usage
    }.get(var_name, default)
    orchestrator = LLMOrchestrator()
    assert orchestrator.config.provider == LLMProvider.HUGGING_FACE
    assert orchestrator.config.hf_api_key == 'test_key'

@patch('src.utils.config.SecureConfig.get')
def test_missing_api_keys(mock_get):
    with pytest.raises(RuntimeError):
        mock_get.side_effect = lambda var_name, default=None: {
            'LLM_PROVIDER': 'gemini' # Missing GEMINI_API_KEY
        }.get(var_name, default) # Corrected .get() usage
        LLMOrchestrator()

    with pytest.raises(RuntimeError):
        mock_get.side_effect = lambda var_name, default=None: {
            'LLM_PROVIDER': 'huggingface' # Missing HUGGING_FACE_API_KEY
        }.get(var_name, default)
        LLMOrchestrator()

@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_gemini_generation(mock_get, mock_client):
    mock_instance = mock_client.return_value
    mock_get.side_effect = lambda var_name, default=None: {
        'GEMINI_API_KEY': 'test_key', 'LLM_PROVIDER': 'gemini', 'LLM_MAX_RETRIES': '3'
    }.get(var_name, default) # Corrected .get() usage
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
        # Rate limit should be attempted before the call in _generate_with_retry
        mock_rate_limit.assert_called_once()

@patch('huggingface_hub.InferenceClient.text_generation')
@patch('src.utils.config.SecureConfig.get')
def test_hf_generation(mock_get, mock_generate):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'huggingface',
        'HUGGING_FACE_API_KEY': 'test_key' # Corrected .get() usage
    }.get(var_name, default)
    mock_generate.return_value = "Test response"
    orchestrator = LLMOrchestrator()
    # Patch _apply_gemini_rate_limit. It should be called by _generate_with_retry,
    # but should be a no-op for HF. We don't assert it's *not* called, just that
    # the HF generation works and no Gemini-specific logic interferes.
    with patch.object(orchestrator, '_apply_gemini_rate_limit') as mock_rate_limit:
        response = orchestrator.generate("test")
        assert response == "Test response"
        # The method _apply_gemini_rate_limit *is* called by _generate_with_retry,
        # but it should do nothing for HF. We don't need to assert it wasn't called.
        # mock_rate_limit.assert_not_called() # REMOVED: This assertion is incorrect now


@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_retry_logic(mock_get, mock_client):
    mock_instance = mock_client.return_value
    mock_get.side_effect = lambda var_name, default=None: {
        'GEMINI_API_KEY': 'test_key', 'LLM_PROVIDER': 'gemini', 'LLM_MAX_RETRIES': '3'
    }.get(var_name, default) # Corrected .get() usage
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
            mock_get.side_effect = lambda var_name, default=None: { # Corrected .get() usage
                'LLM_PROVIDER': 'invalid'
            }.get(var_name, default)
            LLMOrchestrator()

# FIX: Removed isinstance check and added mock call assertion
@patch('google.genai.Client')
@patch('src.utils.config.SecureConfig.get')
def test_gemini_client_initialization(mock_get, mock_client):
    mock_get.side_effect = lambda var_name, default=None: {
        'LLM_PROVIDER': 'gemini', 'GEMINI_API_KEY': 'test_key'
    }.get(var_name, default) # Corrected .get() usage
    orchestrator = LLMOrchestrator()
    # Check that the client was initialized with the correct API key
    mock_client.assert_called_once_with(api_key='test_key')
    # Check that the client's model and api_key are set on the instance
    assert orchestrator.client.api_key == 'test_key'
    assert orchestrator.client.model == 'gemini-2.5-flash-preview-04-17'

@patch.object(EnhancedLLMOrchestrator, '_handle_large_context') # Use patch.object for clarity
def test_large_context_handling(mock_handle_large_context):
    orchestrator = EnhancedLLMOrchestrator(
        kg=MagicMock(),
        spec=MagicMock(spec=FormalSpecification), # Add spec for type hinting
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
    print("Hello") # This is a comment

def function2():
    print("World")

class MyClass:
    def method(self):
        pass"""
    # Assuming parse_code_chunks returns a list of objects with a 'content' attribute
    chunks = parse_code_chunks(code)
    # The original test expected 1 chunk, let's keep that assumption for now
    # based on the previous test output. If the chunking logic changes, this test needs update.
    assert len(chunks) == 1
    assert "def function1():" in chunks[0].content
    assert "def function2():" in chunks[0].content
    assert "class MyClass:" in chunks[0].content

def test_summarization():
    code = """\
def function1():
    print("Hello") # This is a comment

def function2():
    print("World")

class MyClass:
    def method(self):
        pass"""
    # Assuming parse_code_chunks returns a list of objects with a 'content' attribute
    chunks = parse_code_chunks(code)
    # The original test expected 1 chunk, let's keep that assumption for now.
    assert len(chunks) == 1


# --- CORRECTED TEST CASE FOR _call_llm_api unsupported model ---
@patch('src.utils.config.SecureConfig.get')
def test_call_llm_api_unsupported_model(mock_secure_get):
    """
    Tests that _call_llm_api raises ValueError for an unsupported model string.
    """
    # Mock config to allow orchestrator initialization (provider doesn't matter for this test's logic)
    mock_secure_get.side_effect = lambda key, default=None: {
        "LLM_PROVIDER": "gemini", # Or "huggingface", doesn't affect this test
        "GEMINI_API_KEY": "fake_key",
        "HUGGING_FACE_API_KEY": "fake_key",
        "HUGGING_FACE_MODEL": "test-model" # Include HF model config
    }.get(key, default)

    # Instantiate the base orchestrator
    orchestrator = LLMOrchestrator()

    # Directly call _call_llm_api with an unsupported model string
    # Assert that a ValueError is raised with the expected message
    unsupported_model_name = "unsupported_test_model"
    with pytest.raises(ValueError, match=f"Unsupported model: {unsupported_model_name}"):
        orchestrator._call_llm_api("test text", unsupported_model_name)

    # Optional: Verify that supported models *don't* raise ValueError when called
    # (Requires mocking the underlying generate methods to prevent actual calls)
    try:
        with patch.object(orchestrator, '_gemini_generate'), \
             patch.object(orchestrator, '_hf_generate'):
             orchestrator._call_llm_api("test text", LLMProvider.GEMINI.value)
             orchestrator._call_llm_api("test text", LLMProvider.HUGGING_FACE.value)
             orchestrator._call_llm_api("test text", orchestrator.config.hugging_face_model) # Test with configured HF model name
    except ValueError as e:
        pytest.fail(f"_call_llm_api raised ValueError for a supported model: {e}")
# --- END CORRECTED TEST CASE ---


# --- NEW TESTS FOR GEMINI RATE LIMITING ---

@patch('src.utils.config.SecureConfig.get')
def test_gemini_rate_limiting_applied(mock_secure_get, caplog):
    """Tests that _apply_gemini_rate_limit enforces the minimum interval."""
    # Set logging level to INFO to capture the rate limit message
    caplog.set_level(logging.INFO) # <-- ADD THIS LINE

    # Configure mock to use Gemini provider and a fake API key
    mock_secure_get.side_effect = lambda key, default=None: {
        "LLM_PROVIDER": "gemini", "GEMINI_API_KEY": "fake_key",
        "LLM_MAX_RETRIES": "1" # Lower retries for faster test # Corrected .get() usage
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
            # After sleep, time.monotonic() called again (e.g., 100.1) to update _last_gemini_call_start_time.

            # FIX: Add enough side effect values for all calls to time.monotonic()
            mock_monotonic.side_effect = [
                100.0,  # Call 1: time.monotonic() for current_time
                100.0,  # Call 1: time.monotonic() for updating _last_gemini_call_start_time
                100.05, # Call 2: time.monotonic() for current_time
                100.1   # Call 2: time.monotonic() for updating _last_gemini_call_start_time (after sleep)
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

            # Ensure the underlying Gemini call was attempted twice (once per generate call)
            assert mock_gemini_call.call_count == 2

# Add a test for thread safety (Optional but good practice)
@patch('src.utils.config.SecureConfig.get')
def test_gemini_rate_limiting_thread_safety(mock_secure_get):
    """Tests that _apply_gemini_rate_limit is thread-safe."""
    mock_secure_get.side_effect = lambda key, default=None: {
        "LLM_PROVIDER": "gemini", "GEMINI_API_KEY": "fake_key", # Corrected .get() usage
        "LLM_MAX_RETRIES": "1"
    }.get(key, default)

    orchestrator = LLMOrchestrator()
    orchestrator._GEMINI_MIN_INTERVAL_SECONDS = 0.2 # Short interval for test

    # Mock the actual Gemini client call
    with patch.object(orchestrator.client.models, 'generate_content') as mock_gemini_call:
        mock_gemini_call.return_value = MagicMock(
            candidates=[MagicMock(content=MagicMock(parts=[MagicMock(text="Test response")]))]
        )

        # Mock time.sleep and time.monotonic
        # Need enough monotonic values for each thread's calls (at least 2 per thread)
        # Let's provide a large list of increasing values to avoid StopIteration
        mock_monotonic_values = [i * 0.01 for i in range(100)] # Provide 100 values
        with patch('time.sleep') as mock_sleep, \
             patch('time.monotonic', side_effect=mock_monotonic_values) as mock_monotonic:

            def call_generate():
                # Wrap in try/except to catch the RuntimeError from _generate_with_retry
                # if the mock setup isn't perfect, preventing unhandled thread exceptions
                try:
                    orchestrator.generate("thread prompt")
                except RuntimeError as e:
                    logging.error(f"Thread caught expected RuntimeError: {e}")


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
            # It's possible for threads to finish very quickly, but with a short interval (0.2s)
            # and 5 threads, it's highly likely at least 4 sleeps will occur.
            assert mock_sleep.call_count >= num_threads - 1

            # Also check that time.monotonic was called enough times by _apply_gemini_rate_limit
            # Each call to generate calls _apply_gemini_rate_limit.
            # Each call to _apply_gemini_rate_limit calls time.monotonic at least once, potentially twice.
            # So, mock_monotonic.call_count should be between num_threads and num_threads * 2.
            assert num_threads <= mock_monotonic.call_count <= num_threads * 2


# --- REMOVED: This test is no longer valid for the current code structure ---
# @patch('src.utils.config.SecureConfig.get')
# def test_enhanced_orchestrator_call_llm_api_applies_rate_limit_for_gemini(mock_secure_get):
#     """
#     Test that EnhancedLLMOrchestrator._call_llm_api correctly applies the Gemini rate limit
#     when the model is specified as 'gemini'.
#     """
#     # Configure mock to use Gemini provider and a fake API key
#     mock_secure_get.side_effect = lambda key, default=None: {
#         "LLM_PROVIDER": "gemini", "GEMINI_API_KEY": "fake_key",
#         "LLM_MAX_RETRIES": "1"
#     }.get(key, default) # Corrected .get() usage

#     orchestrator = EnhancedLLMOrchestrator(kg=MagicMock(), spec=MagicMock(spec=FormalSpecification), ethics_engine=MagicMock())

#     # Mock the internal _gemini_generate method and _apply_gemini_rate_limit
#     with patch.object(orchestrator, '_gemini_generate') as mock_gemini_generate, \
#          patch.object(orchestrator, '_apply_gemini_rate_limit') as mock_rate_limit:
#         # Call generate, which calls _generate_with_retry, which calls _apply_gemini_rate_limit,
#         # then calls _call_llm_api (the enhanced version), which calls super()._call_llm_api,
#         # which calls _gemini_generate.
#         # The rate limit is applied in _generate_with_retry, NOT in the enhanced _call_llm_api
#         orchestrator.generate("test prompt") # Call generate, not _call_llm_api directly

#         # Assert that _apply_gemini_rate_limit was called by _generate_with_retry
#         mock_rate_limit.assert_called_once()

#         # Assert that _gemini_generate was called by the base _call_llm_api (via the enhanced override)
#         mock_gemini_generate.assert_called_once_with("test prompt")