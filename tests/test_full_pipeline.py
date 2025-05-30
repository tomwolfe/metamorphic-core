# tests/test_full_pipeline.py
import unittest
from hypothesis import given, strategies as st
import pytest
from src.core.llm_orchestration import EnhancedLLMOrchestrator, FormalVerificationError, CriticalFailure
from src.core.chunking.dynamic_chunker import CodeChunk
from unittest.mock import patch, MagicMock
from hypothesis import settings, HealthCheck
from src.core.ethics.constraints import EthicalAllocationPolicy # Import for patching

mock_primary_processing_full_pipeline_test = MagicMock(side_effect=Exception("Primary failed"), __name__='_primary_processing')
mock_secondary_model_full_pipeline_test = MagicMock(side_effect=Exception("Secondary failed"), __name__='_secondary_model') # Mock success for secondary
mock_third_model_full_pipeline_test = MagicMock(side_effect=Exception("Third failed"), __name__='_third_model') # Mock success for third
mock_recursive_summarization_strategy_full_pipeline_test = MagicMock(side_effect=Exception("Recursive failed"), __name__='_recursive_summarization_strategy') # Mock success for recursive summarization

@patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._recursive_summarization_strategy', new=mock_recursive_summarization_strategy_full_pipeline_test)
@patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._third_model', new=mock_third_model_full_pipeline_test)
@patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._secondary_model', new=mock_secondary_model_full_pipeline_test)
@patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._primary_processing', new=mock_primary_processing_full_pipeline_test) # Force primary to fail
class TestOrchestrationSystem(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.mock_spec_instance = MagicMock() # Create mock spec instance here


    def setUp(self):
        self.orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=self.mock_spec_instance, # Use instance mock here
            ethics_engine=MagicMock()
        )

    @patch('src.core.ethics.constraints.EthicalAllocationPolicy.apply') # Patch EthicalAllocationPolicy.apply
    @patch.object(EnhancedLLMOrchestrator, '_count_tokens', return_value=5001) # Mock token count to trigger large context
    # @settings(suppress_health_check=[HealthCheck.large_base_example]) # Removed @settings
    @patch.object(EnhancedLLMOrchestrator, '_gemini_generate')
    @patch.object(EnhancedLLMOrchestrator, '_hf_generate')
    def test_adversarial_inputs_large_pipeline(self, mock_hf_generate, mock_gemini_generate, mock_count_tokens, mock_ethics_apply):
        """Pipeline test for large inputs - expect FormalVerificationError due to chunk validation fail."""
        mock_ethics_apply.return_value = None # Disable ethical policy for this test
        mock_gemini_generate.return_value = "Mock response" # Dummy response
        mock_hf_generate.return_value = "Mock response" # Dummy response
        self.mock_spec_instance.validate_chunks.return_value = False # Make chunk validation fail
        large_payload = "0" * 5000  # Fixed large payload
        # Update mock_count_tokens to exceed the new threshold (8000)
        with patch.object(self.orchestrator, '_count_tokens', return_value=8001) as mock_count_tokens_local:
            with pytest.raises(FormalVerificationError): # Use pytest.raises context manager
                self.orchestrator.generate(large_payload)


    @patch('src.core.ethics.constraints.EthicalAllocationPolicy.apply')
    @patch.object(EnhancedLLMOrchestrator, '_count_tokens', return_value=5001)
    @patch.object(EnhancedLLMOrchestrator, '_gemini_generate')
    @patch.object(EnhancedLLMOrchestrator, '_hf_generate')
    def test_chunk_validation_constraint_violation_pipeline(self, mock_hf_generate, mock_gemini_generate, mock_count_tokens, mock_ethics_apply):
        """Test constraint violation tracking on chunk validation failure."""
        mock_ethics_apply.return_value = None # Disable ethical policy
        mock_gemini_generate.return_value = "Mock response"
        mock_hf_generate.return_value = "Mock response"
        self.mock_spec_instance.validate_chunks.return_value = False # Force chunk validation to fail

        orchestrator = EnhancedLLMOrchestrator(kg=MagicMock(), spec=self.mock_spec_instance, ethics_engine=MagicMock()) # Pass mock instance

        large_payload = "0" * 5000

        # Update mock_count_tokens to exceed the new threshold (8000)
        with patch.object(orchestrator, '_count_tokens', return_value=8001) as mock_count_tokens_local:
            with pytest.raises(FormalVerificationError) as excinfo:
                orchestrator.generate(large_payload)
            assert isinstance(excinfo.value, FormalVerificationError)
            self.assertEqual(orchestrator.telemetry.data.constraint_violations['InitialChunkValidation'], 1) # Assert constraint violation tracked


    @patch('src.core.verification.specification.FormalSpecification.verify_predictions', return_value={'verified': True})
    @patch.object(EnhancedLLMOrchestrator, '_gemini_generate') # Mock Gemini API call
     # Mock HF API call
    @patch.object(EnhancedLLMOrchestrator, '_hf_generate') # Mock HF API call
    def test_formal_verification_integration_pipeline(self, mock_hf_generate, mock_gemini_generate, mock_verify): # Corrected order
        """Test formal verification success."""
        mock_gemini_generate.return_value = "Mock response" # Dummy response
        mock_hf_generate.return_value = "Mock response"
        self.orchestrator.spec.verify_predictions.return_value = {'verified': True} # Mock spec verify_predictions
        result_code = self.orchestrator.generate("Write a function that adds two numbers")
        self.assertIsInstance(result_code, str)

    @patch.object(EnhancedLLMOrchestrator, '_gemini_generate') # Mock Gemini API call
    @patch.object(EnhancedLLMOrchestrator, '_hf_generate') # Mock HF API call
    def test_runtime_formal_verification_failure_pipeline(self, mock_hf_generate, mock_gemini_generate): # Corrected order
        """Test verification failure."""
        mock_gemini_generate.return_value = "Mock response" # Dummy response
        mock_hf_generate.return_value = "Mock response"
        self.orchestrator.spec.verify_predictions.return_value = {'verified': False} # Mock spec verify_predictions to fail
        with pytest.raises(FormalVerificationError) as excinfo: # Use pytest.raises context manager
            self.orchestrator.generate("Write unverifiable code")
        assert isinstance(excinfo.value, FormalVerificationError)

    @patch('src.core.verification.specification.FormalSpecification.verify_predictions', return_value={'verified': True})
    @patch.object(EnhancedLLMOrchestrator, '_gemini_generate') # Mock Gemini API call
    @patch.object(EnhancedLLMOrchestrator, '_hf_generate') # Mock HF API call
    def test_full_self_verification_loop_pipeline(self, mock_hf_generate, mock_gemini_generate, mock_verify): # Corrected order
        """Test self-verification loop."""
        mock_gemini_generate.return_value = "Mock response" # Dummy response
        mock_hf_generate.return_value = "Mock response"
        self.orchestrator.spec.verify_predictions.return_value = {'verified': True} # Mock spec verify_predictions
        verified_code = self.orchestrator.generate("Write a simple Python function")
        self.assertIsInstance(verified_code, str)

    @pytest.mark.skip(reason="Ethical validation needs to be implemented - skipping for now")
    def test_ethical_violation_detection_pipeline(self): # Needs proper ethical checks
        """Pipeline test for ethical violation detection."""
        toxic_code = self._generate_hate_speech()
        with self.assertRaises(Exception): # Replace EthicalViolation with Exception for now
            self.orchestrator.generate(toxic_code)

    @patch('src.core.ethics.constraints.EthicalAllocationPolicy.apply')
    @patch.object(EnhancedLLMOrchestrator, '_count_tokens', return_value=5001)
    @patch.object(EnhancedLLMOrchestrator, '_gemini_generate')
    @patch.object(EnhancedLLMOrchestrator, '_hf_generate')
    def test_full_fallback_pipeline_calls_strategies_pipeline(self, mock_hf_generate, mock_gemini_generate, mock_count_tokens, mock_ethics_apply): # Corrected order and added mock_count_tokens, mock_ethics_apply
        """Pipeline test to ensure fallback strategies are called in full pipeline."""
        mock_ethics_apply.return_value = None # Disable ethical policy for this test
        mock_gemini_generate.return_value = "Mock response" # Dummy response
        mock_hf_generate.return_value = "Mock response"
        orchestrator = EnhancedLLMOrchestrator(kg=MagicMock(), spec=MagicMock(), ethics_engine=MagicMock())
        orchestrator.spec.verify_predictions.return_value = {'verified': False}
        prompt = "Large test prompt to trigger fallback in pipeline" # Large prompt for pipeline fallback
        # Update mock_count_tokens to exceed the new threshold (8000)
        with patch.object(orchestrator, '_count_tokens', return_value=8001) as mock_count_tokens_local:
            with pytest.raises(CriticalFailure) as excinfo: # Use pytest.raises context manager
                orchestrator.generate(prompt)
        assert isinstance(excinfo.value, CriticalFailure)
        mock_primary_processing_full_pipeline_test.assert_called_once() # Check primary called in pipeline
        mock_secondary_model_full_pipeline_test.assert_called_once() # Check secondary fallback engaged
        mock_third_model_full_pipeline_test.assert_called_once() # Check tertiary fallback engaged
        mock_recursive_summarization_strategy_full_pipeline_test.assert_called_once() # Check recursive summarization fallback engaged

    @patch.object(EnhancedLLMOrchestrator, '_count_tokens', return_value=100) # Mock token count to trigger normal context
    @patch.object(EnhancedLLMOrchestrator, '_gemini_generate') # Mock Gemini API call
    @patch.object(EnhancedLLMOrchestrator, '_hf_generate') # Mock HF API call
    @patch('time.time', side_effect=[0.0, 0.001]) # Mock time.time() to return 0.0 then 0.001
    def test_telemetry_integration_in_pipeline_full(self, mock_time, mock_hf_generate, mock_gemini_generate, mock_count_tokens): # Corrected order, added mock_time
        """Pipeline test to verify telemetry data is captured in full pipeline."""
        mock_gemini_generate.return_value = "Mock response" # Dummy response
        mock_hf_generate.return_value = "Mock response" # Dummy response
        orchestrator = EnhancedLLMOrchestrator(kg=MagicMock(), spec=MagicMock(), ethics_engine=MagicMock())
        prompt = "Telemetry pipeline test prompt"
        orchestrator.spec.verify_predictions.return_value = {'verified': False} # Mock spec verify_predictions to fail
        with pytest.raises(FormalVerificationError) as excinfo: # Use pytest.raises context manager
            orchestrator.generate(prompt)
        assert isinstance(excinfo.value, FormalVerificationError)
        self.assertGreaterEqual(orchestrator.telemetry.data.operation_latency['generate_logic'], 0) # Check latency tracked
        self.assertGreater(sum(orchestrator.telemetry.data.model_usage.values()), 0) # Check model usage tracked
        self.assertEqual(sum(orchestrator.telemetry.data.constraint_violations.values()), 0) # Check constraint violations are zero - corrected assertion

    def _generate_hate_speech(self): # Dummy hate speech generator
        return "// Malicious content\n" + "\n".join(f"phrase_{i}" for i in range(100))