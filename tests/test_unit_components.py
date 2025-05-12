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

# Import Z3 components needed for the new test and existing tests
# FIX: Import 'unsat' from z3
from z3 import Int, IntVal, Real, RealVal, Sum, Optimize, ModelRef, ArithRef, sat, unsat # <-- ADDED sat, unsat

# FIX: Import AllocationError from src.core.exceptions
from src.core.exceptions import AllocationError # <-- ADDED AllocationError

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

    # --- FIX START: Patch Optimize class instead of instance ---
    @patch('src.core.optimization.adaptive_token_allocator.Optimize') # Patch Optimize here
    def test_ethical_constraints_unit(self, MockOptimize): # Add MockOptimize to signature
        """Unit test for token allocation respecting ethical constraints."""
        # Configure the mock solver instance
        mock_solver_instance = MockOptimize.return_value
        mock_solver_instance.check.return_value = sat

        # Create a mock Z3 model that solver.model() will return
        mock_z3_model_ref = MagicMock(spec=ModelRef)
        # Define how the mock model should evaluate our Z3 variables
        def mock_eval(z3_var):
            if str(z3_var) == 'tokens_0': return IntVal(150)
            if str(z3_var) == 'model_0': return IntVal(0)
            if str(z3_var) == 'tokens_1': return IntVal(150)
            if str(z3_var) == 'model_1': return IntVal(0)
            return IntVal(0) # Default for any other variable

        mock_z3_model_ref.eval.side_effect = mock_eval
        mock_solver_instance.model.return_value = mock_z3_model_ref

        chunks = [CodeChunk(content="def func1(): pass", estimated_tokens=50), CodeChunk(content="class Class1: pass", estimated_tokens=60)] # Add token estimates
        model_costs = {  # Mock model costs
            'gemini': {'effective_length': 8000, 'cost_per_token': 0.000001},
            'gpt-4': {'effective_length': 8000, 'cost_per_token': 0.00003}
        }

        # Patch the _model_cost method itself, as its internal logic is tested separately
        # This allows us to focus on the allocation logic and the structure of the cost expression
        with patch.object(self.allocator, '_model_cost') as mock_model_cost:
             # Make _model_cost return a simple Z3 Real variable (or ArithRef) for testing the Sum
             mock_model_cost.return_value = Real('cost_term')

             allocation = self.allocator.allocate(chunks, model_costs)

             self.assertIsInstance(allocation, dict, "Allocation should be a dictionary")
             # Check the structure of the returned allocation based on our mock model
             self.assertEqual(allocation, {0: (150, 'gemini'), 1: (150, 'gemini')})

             # Verify _model_cost was called for each chunk
             self.assertEqual(mock_model_cost.call_count, len(chunks))
             # Verify minimize was called on the solver
             mock_solver_instance.minimize.assert_called_once()
             # Verify the argument to minimize is a Z3 expression (Sum of cost_terms)
             minimize_arg = mock_solver_instance.minimize.call_args[0][0]
             self.assertIsInstance(minimize_arg, ArithRef) # Sum is an arithmetic expression
    # --- FIX END ---


    # --- FIX START: Patch Optimize class instead of instance ---
    @patch('src.core.optimization.adaptive_token_allocator.Optimize') # Patch Optimize here
    def test_budget_exhaustion_unit(self, MockOptimize): # Add MockOptimize to signature
        """Unit test for handling budget exhaustion by TokenAllocator."""
        # Configure the mock solver instance that Optimize() will return
        mock_solver_instance = MockOptimize.return_value
        mock_solver_instance.check.return_value = unsat

        chunks = [CodeChunk(content="chunk1", estimated_tokens=200), CodeChunk(content="chunk2", estimated_tokens=200)] # High token chunks
        model_costs = {  # Mock model costs
            'gemini': {'effective_length': 8000, 'cost_per_token': 0.000001},
            'gpt-4': {'effective_length': 8000, 'cost_per_token': 0.00003}
        }

        with pytest.raises(AllocationError, match="No ethical allocation possible even without cost minimization."): # Match the more specific error message
            self.allocator.allocate(chunks, model_costs)

        # You can add assertions on mock_solver_instance if needed, e.g.:
        mock_solver_instance.check.assert_called()
    # --- FIX END ---


    # --- NEW TEST CASE FOR _model_cost ---
    def test_model_cost_calculation_unit(self):
        """Unit test for TokenAllocator._model_cost method."""
        allocator = TokenAllocator() # Instantiated in setUp for other tests, or create new

        # Mock Z3 variables and solver model for testing _model_cost directly
        mock_solver_model = MagicMock(spec=ModelRef)

        # Define a sample models_list for the test
        sample_models_list = [
            {'name': 'gemini', 'cost_per_token': 0.000001, 'effective_length': 8000},
            {'name': 'gpt-4', 'cost_per_token': 0.00003, 'effective_length': 8000},
        ]

        # Test case 1: Gemini, 1000 tokens
        model_idx_var1 = Int('model_idx_1')
        tokens_var1 = Int('tokens_1')

        # Simulate solver_model.eval behavior for case 1
        def eval_side_effect_gemini(z3_var):
            if str(z3_var) == str(model_idx_var1): return IntVal(0) # Gemini is index 0
            if str(z3_var) == str(tokens_var1): return IntVal(1000)
            return IntVal(0) # Default for other variables
        mock_solver_model.eval = MagicMock(side_effect=eval_side_effect_gemini)

        # The _model_cost method no longer takes solver_model
        cost1_expr = allocator._model_cost(model_idx_var1, tokens_var1, sample_models_list)

        # To verify the Z3 expression, we can't directly compare floats easily.
        # We can check if the structure is roughly correct or simplify and evaluate if possible.
        # For simplicity, let's check if the expression is an ArithRef (Z3 arithmetic expression)
        self.assertIsInstance(cost1_expr, ArithRef)
        # print(f"Cost1 Z3 Expr: {cost1_expr}") # For manual inspection

        # Test case 2: GPT-4, 500 tokens
        model_idx_var2 = Int('model_idx_2')
        tokens_var2 = Int('tokens_2')

        # Simulate solver_model.eval behavior for case 2
        def eval_side_effect_gpt4(z3_var):
            if str(z3_var) == str(model_idx_var2): return IntVal(1) # GPT-4 is index 1
            if str(z3_var) == str(tokens_var2): return IntVal(500)
            return IntVal(0)
        mock_solver_model.eval = MagicMock(side_effect=eval_side_effect_gpt4)

        # The _model_cost method no longer takes solver_model
        cost2_expr = allocator._model_cost(model_idx_var2, tokens_var2, sample_models_list)
        self.assertIsInstance(cost2_expr, ArithRef)
        # print(f"Cost2 Z3 Expr: {cost2_expr}")

        # Expected calculation for GPT-4, 500 tokens:
        # base_cost = 500 * 0.00003 = 0.015
        # complexity_penalty = (500*500) / 1000 = 250000 / 1000 = 250
        # total_cost_approx = 0.015 + 250 = 250.015
        # We can't directly assert this float value from the Z3 expression easily without solving.
        # The test primarily ensures the method runs and produces a Z3 expression.


class TestRecursiveSummarizer(unittest.TestCase):
    def setUp(self):
        self.mock_llm = MagicMock()
        self.mock_verifier = MagicMock()
        self.mock_telemetry = MagicMock()  # Mock Telemetry
        self.summarizer = RecursiveSummarizer(self.mock_llm, self.mock_verifier, self.mock_telemetry) # Pass telemetry
        self.mock_llm._count_tokens.return_value = 10 # Mock token count # Ensure LLM mock has _count_tokens


    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    def test_recursive_summarization_depth_control(self, mock_generate_summary):
        """Unit test for recursive summarization depth control."""
        mock_generate_summary.return_value = "Mock summary string"
        self.mock_verifier.verify.return_value = True # Mock verifier to always pass
        self.mock_verifier.validate_chunks.return_value = True # Mock chunk validation to always pass
        code = "def func1(): pass\n\ndef func2(): pass\n\ndef func3(): pass" # Example code
        summary = self.summarizer.summarize_code_recursively(code, depth=2) # Test with depth 2
        mock_generate_summary.assert_called() # Check if LLM generate was called
        # The number of calls depends on chunking and window size, just check it was called at least once
        assert mock_generate_summary.call_count >= 1

    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    def test_recursive_summarization_depth_one(self, mock_generate_summary):
        """Unit test for recursive summarization depth control."""
        mock_generate_summary.return_value = "Mock summary string"
        self.mock_verifier.verify.return_value = True # Mock verifier to always pass
        self.mock_verifier.validate_chunks.return_value = True # Mock chunk validation to always pass
        code = "def short_func(): pass" # Short code for single chunk
        summary = self.summarizer.summarize_code_recursively(code, depth=1) # Test with depth 1
        self.assertIsInstance(summary, str, "Summary should be a string")
        mock_generate_summary.assert_called_once()


    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    def test_summary_pre_verification_failure(self, mock_generate_summary): # Changed test name to reflect pre-verification failure
        """Unit test for handling summary verification failure."""
        mock_generate_summary.return_value = "mock summary" # Return string for summary # Corrected mock to return string
        self.mock_verifier.validate_chunks.return_value = False # Mock chunk validation to fail # Changed to False
        code = "def failing_func(): pass"
        with pytest.raises(FormalVerificationError, match="Chunk failed pre-summarization validation"): # Expect FormalVerificationError
            self.summarizer.summarize_code_recursively(code)
        mock_generate_summary.assert_not_called() # LLM should not be called if validation fails


    # FIX: Remove the patch on _generate_verified_summary
    # @patch('src.core.chunking.recursive_summarizer.RecursiveSummarizer._generate_verified_summary')
    @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
    # FIX: Correct the signature to remove mock_verified_summary
    def test_summary_retry_mechanism_unit(self, mock_generate_summary): # Corrected signature
        """Unit test for retry mechanism in verified summary generation."""
        mock_generate_summary.return_value = "Mock summary string" # Re-add mock for self.llm.generate to return string
        # FIX: Configure mock_verifier_verify to fail initially, then succeed
        # mock_verified_summary.side_effect = ["summary1", "summary2"] # Mock _generate_verified_summary to return summaries
        # Patch self.verifier.verify *within* this test to control its behavior when called by the real _generate_summary
        # FIX: Set side_effect on mock_verifier_verify to trigger retries
        with patch.object(self.mock_verifier, 'verify', side_effect=[False, False, True]) as mock_verifier_verify: # <-- Patch here, set side_effect
            self.mock_verifier.validate_chunks.return_value = True # Mock chunk validation to always pass
            code = "def retry_func(): pass"
            summary = self.summarizer.summarize_code_recursively(code, depth=1) # FIX: Set depth=1
            # print(f"LLM generate call count: {mock_generate_summary.call_count}") # Debug print
            # print(f"Verifier verify call count: {self.mock_verifier.verify.call_count}") # Debug print
            mock_generate_summary.assert_called()
            # The number of calls to _generate_summary depends on the retry logic within _generate_verified_summary
            # and the number of chunks. With a single chunk and _generate_verified_summary mocked,
            # _generate_summary is called once by _generate_verified_summary.
            self.assertEqual(mock_generate_summary.call_count, 3, "LLM generate should be called 3 times due to retry logic")
            # FIX: Assertion should check the summary returned by _generate_summary
            self.assertEqual(summary, "Mock summary string", "Should return the summary generated by _generate_summary") # Corrected assertion
            # Verify that self.mock_verifier.verify was called by the real _generate_summary
            # FIX: Assertion count should be 3
            self.assertEqual(mock_verifier_verify.call_count, 3, "Verifier verify should be called 3 times due to retry logic") # Corrected assertion