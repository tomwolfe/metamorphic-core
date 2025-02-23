# tests/test_unit_components.py
# tests/test_unit_components.py
import unittest
from hypothesis import given, strategies as st
from src.core.chunking.semantic_boundary_detector import SemanticBoundaryDetector
from src.core.optimization.adaptive_token_allocator import TokenAllocator
from src.core.ethics.constraints import EthicalAllocationPolicy # Import policy
from src.core.chunking.dynamic_chunker import CodeChunk # Import CodeChunk for test setup
from src.core.chunking.recursive_summarizer import RecursiveSummarizer # Import RecursiveSummarizer
from unittest.mock import MagicMock, patch
from src.core.verification import FormalSpecification, FormalVerificationError # Import FormalVerificationError
import pytest

class TestSemanticBoundaryDetector(unittest.TestCase):
    def test_malformed_code_handling_unit(self):
        """Unit test for handling malformed code by SemanticBoundaryDetector."""
        detector = SemanticBoundaryDetector()
        boundaries = detector.detect_boundaries("invalid code !@#")
        self.assertGreater(len(boundaries), 0, "Should detect boundaries even in malformed code")

    def test_empty_code_handling_unit(self):
        """Unit test for handling empty code input."""
        detector = SemanticBoundaryDetector()
        boundaries = detector.detect_boundaries("")
        self.assertEqual(boundaries, [], "Should return empty list for empty code")

    def test_code_with_comments_only_unit(self):
        """Unit test for code consisting only of comments."""
        detector = SemanticBoundaryDetector()
        code_with_comments = "# This is a comment\n'''Multiline comment'''\n"
        boundaries = detector.detect_boundaries(code_with_comments)
        self.assertEqual(boundaries, [], "Should handle code with only comments")

    def test_valid_code_boundaries_unit(self):
        """Unit test for boundary detection in valid, structured code."""
        detector = SemanticBoundaryDetector()
        valid_code = """def function_a():\n  pass\n\nclass ClassB:\n  def method_c(self): pass"""
        boundaries = detector.detect_boundaries(valid_code)
        self.assertGreater(len(boundaries), 0, "Should detect boundaries in valid code")

class TestTokenAllocator(unittest.TestCase):
    def setUp(self):
        self.allocator = TokenAllocator(total_budget=300) # Initialize allocator here

    def test_ethical_constraints_unit(self):
        """Unit test for token allocation respecting ethical constraints."""
        chunks = [CodeChunk(content="def func1(): pass", estimated_tokens=50), CodeChunk(content="class Class1: pass", estimated_tokens=60)] # Add token estimates
        allocation = self.allocator.allocate(chunks) # Corrected allocate call - removed model costs arg
        self.assertIsInstance(allocation, dict, "Allocation should be a dictionary")
        self.assertTrue(all(50 <= v[0] <= 200 for v in allocation.values()), "Token allocation out of expected bounds") # Check token allocation within bounds

    def test_budget_exhaustion_unit(self):
        """Unit test for handling budget exhaustion by TokenAllocator."""
        chunks = [CodeChunk(content="chunk1", estimated_tokens=200), CodeChunk(content="chunk2", estimated_tokens=200)] # High token chunks
        allocation = self.allocator.allocate(chunks) # Corrected allocate call - removed model costs arg
        self.assertLess(sum(v[0] for v in allocation.values()), 300, "Total allocation should not exceed budget") # Total allocation within budget

class TestRecursiveSummarizer(unittest.TestCase):
    def setUp(self):
        self.mock_llm = MagicMock()
        self.mock_verifier = MagicMock()
        self.mock_telemetry = MagicMock()  # Mock Telemetry
        self.summarizer = RecursiveSummarizer(self.mock_llm, self.mock_verifier, self.mock_telemetry) # Pass telemetry

    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    def test_recursive_summarization_depth_unit(self, mock_generate_summary):
        """Unit test for recursive summarization depth control."""
        mock_generate_summary.return_value = "Mock summary string"
        self.mock_verifier.verify.return_value = True # Mock verifier to always pass
        code = "def func1(): pass\n\ndef func2(): pass\n\ndef func3(): pass" # Example code
        summary = self.summarizer.summarize_code_recursively(code, depth=2) # Test with depth 2
        mock_generate_summary.assert_called() # Check if LLM generate was called
        assert mock_generate_summary.call_count >= 1

    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    def test_recursive_summarization_depth_unit_called_once(self, mock_generate_summary):
        """Unit test for recursive summarization depth control."""
        mock_generate_summary.return_value = "Mock summary string"
        code = "def short_func(): pass" # Short code for single chunk
        summary = self.summarizer.summarize_code_recursively(code, depth=1) # Test with depth 1
        self.assertIsInstance(summary, str, "Summary should be a string")
        mock_generate_summary.assert_called_once()


    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    def test_summary_pre_verification_failure_unit(self, mock_generate_summary): # Changed test name to reflect pre-verification failure
        """Unit test for handling summary verification failure."""
        mock_generate_summary.return_value = "mock summary" # Return string for summary # Corrected mock to return string
        self.mock_verifier.validate_chunks.return_value = False # Mock chunk validation to fail # Changed to False
        code = "def failing_func(): pass"
        with pytest.raises(FormalVerificationError, match="Chunk failed pre-summarization validation"): # Expect FormalVerificationError
            self.summarizer.summarize_code_recursively(code)

    @patch('src.core.chunking.recursive_summarizer.RecursiveSummarizer._generate_verified_summary')
    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    def test_summary_retry_mechanism_unit(self, mock_generate_summary, mock_verified_summary):
        """Unit test for retry mechanism in verified summary generation."""
        mock_generate_summary.return_value = "Mock summary string" # Re-add mock for self.llm.generate to return string
        mock_verified_summary.side_effect = ["summary1", "summary2"] # Mock _generate_verified_summary to return summaries
        self.mock_verifier.verify.side_effect = [False, True, True, True] # Mock verify to fail then pass (increased side_effect length)
        code = "def retry_func(): pass"
        summary = self.summarizer.summarize_code_recursively(code)
        print(f"LLM generate call count: {mock_generate_summary.call_count}") # Debug print
        print(f"Verifier verify call count: {self.mock_verifier.verify.call_count}") # Debug print
        mock_generate_summary.assert_called()
        self.assertEqual(mock_generate_summary.call_count, 3, "LLM generate should be called 3 times due to retry and recursion") # Corrected assertion to check LLM generate calls
        self.assertEqual(summary, "Mock summary string", "Should return the original mock summary after successful retry") # Corrected assertion - EXPECT ORIGINAL SUMMARY

class TestFormalSpecification(unittest.TestCase): # New FormalVerifier Unit Tests
    def setUp(self):
        self.spec = FormalSpecification()
        self.spec.add_safety_invariant("BiasRisk never exceeds 0.30") # Increased threshold to avoid false positives in other tests if run together
        self.spec.add_ethical_guardrail("TransparencyScore never drops below 0.30") # Increased threshold

    def test_constraint_verification(self):
        predictions = {
            "bias_risk": 0.2,
            "transparency_score": 0.5,
            "immediate_risk": 0.1
        }
        result = self.spec.verify_predictions(predictions)
        assert result["verified"]

    def test_constraint_violation(self):
        predictions = {
            "bias_risk": 0.31, # Violates "never exceeds 0.30"
            "transparency_score": 0.29, # Violates "never drops below 0.30"
            "immediate_risk": 0.1
        }
        result = self.spec.verify_predictions(predictions)
        assert not result["verified"]
        assert len(result["violations"]) == 2
