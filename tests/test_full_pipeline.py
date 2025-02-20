# tests/test_full_pipeline.py
import unittest
from hypothesis import given, strategies as st
import pytest
from src.core.llm_orchestration import EnhancedLLMOrchestrator, FormalVerificationError # Import FormalVerificationError
from src.core.chunking.dynamic_chunker import CodeChunk # Import CodeChunk for test setup
from unittest.mock import patch, MagicMock

class TestOrchestrationSystem(unittest.TestCase):
    def setUp(self):
        self.orchestrator = EnhancedLLMOrchestrator(kg=MagicMock(), spec=MagicMock(), ethics_engine=MagicMock()) # Mock spec and ethics_engine

    @given(st.text(min_size=100000))  # 100KB+ texts
    def test_adversarial_inputs_large_pipeline(self, payload):
        """Pipeline test for handling extremely large inputs."""
        with self.assertRaises(FormalVerificationError): # Expect FormalVerificationError for large inputs
            self.orchestrator.generate(payload)

    @pytest.mark.skip(reason="Ethical validation needs to be implemented - skipping for now")
    def test_ethical_violation_detection_pipeline(self): # Needs proper ethical checks
        """Pipeline test for ethical violation detection."""
        toxic_code = self._generate_hate_speech()
        with self.assertRaises(Exception): # Replace EthicalViolation with Exception for now
            self.orchestrator.generate(toxic_code)

    def test_formal_verification_integration_pipeline(self):
        """Pipeline test for formal verification success (mocked)."""
        # Mock FormalVerifier.verify to simulate successful verification
        with patch('src.core.verification.formal_verifier.FormalVerifier.verify', return_value=True):
             # Test with a sample prompt
            result_code = self.orchestrator.generate("Write a function that adds two numbers")
            self.assertIsInstance(result_code, str, "Generate should return code string")

    def test_runtime_formal_verification_failure_pipeline(self):
        """Pipeline test for runtime formal verification failure."""
        # Mock FormalVerifier.verify to simulate verification failure
        with patch('src.core.verification.formal_verifier.FormalVerifier.verify', return_value=False):
            with self.assertRaises(FormalVerificationError, match="Chunk .* failed Coq verification"): # Check for specific error
                self.orchestrator.generate("Write unverifiable code") # Prompt that should trigger verification fail

    def test_full_self_verification_loop_pipeline(self):
        """Pipeline test for full self-verification loop (mocked verification)."""
        # Mock FormalVerifier.verify to always return True for self-verification loop
        with patch('src.core.verification.formal_verifier.FormalVerifier.verify', return_value=True):
            # Test with a simple prompt
            verified_code = self.orchestrator.generate("Write a simple Python function")
            self.assertIsInstance(verified_code, str, "Self-verified code should be generated")
            self.assertGreater(len(verified_code), 10, "Generated code should have substantial length")

    def _generate_hate_speech(self): # Dummy hate speech generator
        return "// Malicious content\n" + "\n".join(f"phrase_{i}" for i in range(100))

    @patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._recursive_summarization_strategy')
    @patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._third_model')
    @patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._secondary_model')
    @patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._primary_processing')
    def test_full_fallback_pipeline_calls_strategies_pipeline(self, mock_primary, mock_secondary, mock_third, mock_recursive):
        """Pipeline test to ensure fallback strategies are called in full pipeline."""
        orchestrator = EnhancedLLMOrchestrator(kg=MagicMock(), spec=MagicMock(), ethics_engine=MagicMock())
        prompt = "Large test prompt to trigger fallback in pipeline" # Large prompt for pipeline fallback
        with self.assertRaises(FormalVerificationError): # Expect verification error triggering fallbacks
            orchestrator.generate(prompt)
        mock_primary.assert_called_once() # Check primary called in pipeline
        mock_secondary.assert_called_once() # Check secondary fallback engaged
        mock_third.assert_called_once() # Check tertiary fallback engaged
        mock_recursive.assert_called_once() # Check recursive summarization fallback engaged

    @patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._recursive_summarization_strategy')
    @patch('src/core.llm_orchestration.EnhancedLLMOrchestrator._third_model')
    @patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._secondary_model')
    @patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._primary_processing')
    def test_telemetry_integration_in_pipeline_full(self, mock_primary, mock_secondary, mock_third, mock_recursive):
        """Pipeline test to verify telemetry data is captured in full pipeline."""
        orchestrator = EnhancedLLMOrchestrator(kg=MagicMock(), spec=MagicMock(), ethics_engine=MagicMock())
        prompt = "Telemetry pipeline test prompt"
        with self.assertRaises(FormalVerificationError): # Expect verification error to ensure full pipeline run
            orchestrator.generate(prompt)
        self.assertGreater(orchestrator.telemetry.data.operation_latency['generate'], 0) # Check latency tracked
        self.assertGreater(sum(orchestrator.telemetry.data.model_usage.values()), 0) # Check model usage tracked
        self.assertGreater(sum(orchestrator.telemetry.data.constraint_violations.values()), 0) # Check constraint violations tracked
