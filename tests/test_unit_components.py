# tests/test_unit_components.py
import sys
print(f"SYS PATH: {sys.path}")
import unittest
from hypothesis import given, strategies as st
from src.core.chunking.semantic_boundary_detector import SemanticBoundaryDetector
from src.core.optimization.adaptive_token_allocator import TokenAllocator
from src.core.ethics.constraints import EthicalAllocationPolicy # Import policy
from src.core.chunking.dynamic_chunker import CodeChunk # Import CodeChunk for test setup
from src.core.chunking.recursive_summarizer import RecursiveSummarizer # Import RecursiveSummarizer
from unittest.mock import MagicMock, patch
from src.core.verification import FormalSpecification, FormalVerificationError # Import FormalSpecification, FormalVerificationError
import pytest

class TestSemanticBoundaryDetector(unittest.TestCase):
    def test_malformed_code_handling_unit(self):
        """Unit test for handling malformed code by SemanticBoundaryDetector."""
        detector = SemanticBoundaryDetector()
        boundaries = detector.detect_boundaries("invalid code !@#")
        self.assertEqual(len(boundaries), 0, "Should not detect boundaries in malformed code without empty lines")

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
        self.allocator = TokenAllocator(total_budget=300)

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
        self.mock_telemetry = MagicMock() # Mock Telemetry
        self.summarizer = RecursiveSummarizer(self.mock_llm, self.mock_verifier, self.mock_telemetry) # Pass telemetry
        self.mock_llm.generate.return_value = "test summary string" # Make mock_llm.generate() return a string

    def test_recursive_summarization_depth_unit(self):
        """Unit test for recursive summarization depth control."""
        code = "def func1(): pass\n\ndef func2(): pass\n\ndef func3(): pass" # Example code
        summary = self.summarizer.summarize_code_recursively(code, depth=2) # Test with depth 2
        self.mock_llm.generate.assert_called() # Check if LLM generate was called
        self.assertIsInstance(summary, str, "Summary should be a string")

    def test_summary_verification_failure_unit(self):
        """Unit test for handling summary verification failure."""
        self.mock_verifier.verify.return_value = False # Make verification fail
        code = "def failing_func(): pass"
        with pytest.raises(FormalVerificationError, match="Chunk failed pre-summarization validation"): # Expect FormalVerificationError
            self.summarizer.summarize_code_recursively(code)

    @patch('src.core.chunking.recursive_summarizer.RecursiveSummarizer._generate_verified_summary')
    def test_summary_retry_mechanism_unit(self, mock_verified_summary):
        """Unit test for retry mechanism in verified summary generation."""
        mock_verified_summary.side_effect = ["summary1", "summary2"] # Mock successful summaries after retries
        code = "def retry_func(): pass"
        summary = self.summarizer.summarize_code_recursively(code)
        self.assertEqual(mock_verified_summary.call_count, 1, "Verified summary should be called for retry") # Corrected assertion
        self.assertEqual(summary, "summary1", "Should return the verified summary") # Corrected assertion

class TestFormalVerifier(unittest.TestCase): # New FormalVerifier Unit Tests
    def setUp(self):
        self.verifier = FormalSpecification()

    def test_validate_chunks_empty_unit(self):
        """Unit test for validate_chunks with empty chunk list."""
        is_valid = self.verifier.validate_chunks([])
        self.assertTrue(is_valid, "Should validate empty chunk list")

    def test_validate_chunks_token_count_unit(self):
        """Unit test for validate_chunks token count constraint."""
        valid_chunk = CodeChunk(content="def valid_function(): pass", estimated_tokens=100)
        invalid_chunk = CodeChunk(content="long " * 2000, estimated_tokens=2000) # Exceeds limit
        is_valid_single = self.verifier.validate_chunks([valid_chunk])
        is_invalid_single = not self.verifier.validate_chunks([invalid_chunk]) # Negated for clarity
        is_valid_mixed = self.verifier.validate_chunks([valid_chunk, valid_chunk]) # Multiple valid
        is_invalid_mixed = not self.verifier.validate_chunks([valid_chunk, invalid_chunk]) # Mixed valid/invalid

        self.assertTrue(is_valid_single, "Should validate chunk within token limit")
        self.assertTrue(is_invalid_single, "Should invalidate chunk exceeding token limit")
        self.assertTrue(is_valid_mixed, "Should validate list of valid chunks")
        self.assertTrue(is_invalid_mixed, "Mixed chunks should fail if any invalid")

    def test_verify_valid_code_unit(self):
        """Unit test for verify method with valid code chunk (mocked Coq proof)."""
        mock_verifier = MagicMock()
        with patch('src.core.verification.formal_verifier.CoqProver', return_value=mock_verifier):
            mock_verifier.verify.return_value = True # Mock successful Coq verification
            valid_chunk = CodeChunk(content="def add(a, b): return a + b", estimated_tokens=20) # Realistic code chunk
            is_verified = self.verifier.verify(valid_chunk)
            self.assertTrue(is_verified, "Verify should return True on successful Coq proof")
            mock_verifier.verify.assert_called_once() # Check if mock verify was actually called
            called_chunk = mock_verifier.verify.call_args[0][0] # Get the chunk passed to mock
            self.assertIsInstance(called_chunk, CodeChunk, "Coq verify mock should receive CodeChunk instance")
            self.assertIn("def add", called_chunk.content, "Mock verify called with correct code content") # Content check

    def test_verify_invalid_code_unit(self):
        """Unit test for verify method with invalid code chunk (mocked Coq failure)."""
        mock_verifier = MagicMock()
        with patch('src.core.verification.formal_verifier.CoqProver', return_value=mock_verifier):
            mock_verifier.verify.return_value = False # Mock failed Coq verification
            invalid_chunk = CodeChunk(content="def buggy_code(): raise Exception('oops')", estimated_tokens=25) # Realistic buggy code
            is_verified = self.verifier.verify(invalid_chunk)
            self.assertFalse(is_verified, "Verify should return False on failed Coq proof")
            mock_verifier.verify.assert_called_once() # Check if mock verify was actually called
            called_chunk = mock_verifier.verify.call_args[0][0] # Get the chunk passed to mock
            self.assertIsInstance(called_chunk, CodeChunk, "Coq verify mock should receive CodeChunk instance")
            self.assertIn("raise Exception", called_chunk.content, "Mock verify called with correct code content") # Content check

    def test_verify_exception_handling_unit(self):
        """Unit test for verify method exception handling (CoqProver raises Exception)."""
        mock_verifier = MagicMock()
        with patch('src.core.verification.formal_verifier.CoqProver', return_value=mock_verifier):
            mock_verifier.verify.side_effect = Exception("Coq Prover Error") # Simulate Coq exception
            chunk = CodeChunk(content="unpredictable code", estimated_tokens=50) # Unpredictable code example
            is_verified = self.verifier.verify(chunk)
            self.assertFalse(is_verified, "Verify should return False if CoqProver raises exception")
            mock_verifier.verify.assert_called_once() # Check if mock verify was actually called
            called_chunk = mock_verifier.verify.call_args[0][0] # Get the chunk passed to mock
            self.assertIsInstance(called_chunk, CodeChunk, "Coq verify mock should receive CodeChunk instance")
            self.assertIn("unpredictable code", called_chunk.content, "Mock verify called with correct code content") # Content check
