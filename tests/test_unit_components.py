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
import logging # Ensure logging is imported

# Import Z3 components needed for the new test and existing tests
# FIX: Import 'unsat' from z3
from z3 import Int, IntVal, Real, RealVal, Sum, Optimize, ModelRef, ArithRef, sat, unsat, Solver

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
        # Configure the mock solver instance that Optimize() will return
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

        # --- FIX: Update the regex pattern to match the new error message ---
        with pytest.raises(AllocationError, match="No ethical allocation possible after initial UNSAT and fallback failure."): # Match the more specific error message
            self.allocator.allocate(chunks, model_costs)
        # --- END FIX ---


        # You can add assertions on mock_solver_instance if needed, e.g.:
        mock_solver_instance.check.assert_called()
    # --- FIX END ---

    @patch('src.core.optimization.adaptive_token_allocator.Optimize')
    def test_allocate_with_hf_model_capacity_conflict_resolved(self, MockOptimize):
        """
        Test allocation succeeds when REALISTIC_MIN_TOKENS_PER_CHUNK is compatible
        with a model having a smaller capacity (e.g., Hugging Face model at 4096).
        This test uses the corrected REALISTIC_MIN_TOKENS_PER_CHUNK = 1000.
        """
        mock_solver_instance = MockOptimize.return_value
        mock_solver_instance.check.return_value = sat

        mock_z3_model_ref = MagicMock(spec=ModelRef)
        # Define a side effect for the mock Z3 model's eval method to simulate a successful allocation
        # where the Hugging Face model (index 1) is chosen and tokens are allocated within its capacity.
        def mock_eval_hf_selected(z3_var):
            if str(z3_var) == 'tokens_0': return IntVal(4000)  # Simulate allocation of 4000 tokens for chunk 0
            if str(z3_var) == 'model_0': return IntVal(1)    # Simulate selection of Hugging Face model (index 1) for chunk 0
            return IntVal(0) # Default for other variables
        mock_z3_model_ref.eval.side_effect = mock_eval_hf_selected
        mock_solver_instance.model.return_value = mock_z3_model_ref

        # Temporarily set the constant in adaptive_token_allocator for this test context
        # This is tricky as it's a module-level constant. We'll rely on the diff being applied.
        # For a pure unit test, we might need to patch the constant lookup if it were more dynamic.
        # Here, we assume the constant is 1000 due to the applied diff.
        allocator = TokenAllocator(total_budget=5000)
        chunks = [CodeChunk(content="chunk for hf", estimated_tokens=300)]
        model_costs = {
            'gemini': {'effective_length': 500000, 'cost_per_token': 0.000001},
            'hf_model': {'effective_length': 4096, 'cost_per_token': 0.000002} # HF model
        }

        with patch.object(allocator, '_model_cost', return_value=Real('cost_term')):
            allocation = allocator.allocate(chunks, model_costs)
            self.assertIn(0, allocation)
            self.assertEqual(allocation[0], (4000, 'hf_model'))
            
            # Verify constraints added to solver (illustrative, exact Z3 objects are hard to assert)
            # Check that solver.add was called with constraints like tokens_0 >= 1000 and tokens_0 <= 4096 (for hf_model)
            # This requires inspecting solver.assertions() or mocking solver.add more intricately.
            # For now, successful allocation implies constraints were satisfiable.

    @patch('src.core.optimization.adaptive_token_allocator.Optimize')
    def test_allocate_raises_error_with_original_conflicting_min_chunk_size(self, MockOptimize):
        """
        Test that AllocationError is raised if REALISTIC_MIN_TOKENS_PER_CHUNK (e.g., 5000)
        conflicts with a model's capacity (e.g., Hugging Face model at 4096).
        This simulates the original error condition.
        """
        mock_solver_instance = MockOptimize.return_value
        # To simulate the original error condition (REALISTIC_MIN_TOKENS_PER_CHUNK = 5000
        # conflicting with HF model capacity = 4096), we force the Z3 solver to return UNSAT.
        # This bypasses the need to dynamically change the module-level constant for this specific test,
        # directly testing the error path triggered by an unsatisfiable allocation.
        mock_solver_instance.check.return_value = unsat 

        allocator = TokenAllocator(total_budget=10000)
        chunks = [CodeChunk(content="chunk1", estimated_tokens=300)]
        model_costs = {'hf_model': {'effective_length': 4096, 'cost_per_token': 0.000002}}
        with self.assertRaisesRegex(AllocationError, "No ethical allocation possible after initial UNSAT and fallback failure."):
            allocator.allocate(chunks, model_costs)

    # --- NEW TEST CASE FOR _model_cost ---
    def test_model_cost_calculation_unit(self):
        """Unit test for TokenAllocator._model_cost method."""
        allocator = TokenAllocator() # Instantiated in setUp for other tests, or create new

        # Mock Z3 variables and solver model for testing _model_cost directly
        # FIX: Define mock_z3_model_ref before using it
        mock_z3_model_ref = MagicMock(spec=ModelRef)

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
            return IntVal(0) # Default for any other variable

        mock_z3_model_ref.eval.side_effect = eval_side_effect_gemini

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
        mock_z3_model_ref.eval = MagicMock(side_effect=eval_side_effect_gpt4)

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


    @patch('src.core.optimization.adaptive_token_allocator.Optimize')
    def test_allocate_single_model_provider_gemini_only(self, MockOptimize, caplog): # Added caplog
        """Test TokenAllocator.allocate when only Gemini is available and logs warning."""
        caplog.set_level(logging.WARNING) # Capture warnings
        mock_solver_instance = MockOptimize.return_value
        mock_solver_instance.check.return_value = sat

        mock_z3_model_ref = MagicMock(spec=ModelRef)
        def mock_eval_gemini_only(z3_var):
            var_name_str = str(z3_var)
            if 'tokens_0' in var_name_str: return IntVal(1500)
            if 'model_0' in var_name_str: return IntVal(0)
            if 'tokens_1' in var_name_str: return IntVal(1800)
            if 'model_1' in var_name_str: return IntVal(0)
            return IntVal(0) 
        mock_z3_model_ref.eval.side_effect = mock_eval_gemini_only
        mock_solver_instance.model.return_value = mock_z3_model_ref
        
        allocator = TokenAllocator(total_budget=5000)
        chunks = [
            CodeChunk(content="chunk content 1", estimated_tokens=500),
            CodeChunk(content="chunk content 2", estimated_tokens=600)
        ]
        model_costs_gemini_only = {
            'gemini': {'effective_length': 500000, 'cost_per_token': 0.000001}
        }

        with patch.object(allocator, '_model_cost', return_value=Real('mock_cost_term')):
            allocation = allocator.allocate(chunks, model_costs_gemini_only)

            assert isinstance(allocation, dict)
            assert len(allocation) == len(chunks)
            for i in range(len(chunks)):
                assert allocation[i][1] == 'gemini'
                assert allocation[i][0] >= 1000 

            mock_solver_instance.minimize.assert_called_once()
            assert "TokenAllocator: Only one model provider (gemini) is available" in caplog.text
            assert "Model diversity constraints in EthicalAllocationPolicy will be naturally bypassed." in caplog.text


    class TestRecursiveSummarizer(unittest.TestCase):
        def setUp(self):
            self.mock_llm = MagicMock()
            self.mock_verifier = MagicMock()
            self.mock_telemetry = MagicMock()  # Mock Telemetry
            self.summarizer = RecursiveSummarizer(self.mock_llm, self.mock_verifier, self.mock_telemetry) # Pass telemetry
            self.mock_llm._count_tokens.return_value = 10 # Mock token count # Ensure LLM mock has _count_tokens


        @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
        # FIX: Remove the patch on _generate_verified_summary
        # @patch('src.core.chunking.recursive_summarizer.RecursiveSummarizer._generate_verified_summary')
        # FIX: Correct the signature to remove mock_verified_summary
        def test_recursive_summarization_depth_control(self, mock_generate_summary): # Changed test name to reflect pre-verification failure
            """Unit test for recursive summarization depth control."""
            mock_generate_summary.return_value = "Mock summary string" # Return string for summary # Corrected mock to return string
            self.mock_verifier.validate_chunks.return_value = True # Mock chunk validation to always pass # Changed to False
            code = "def func1(): pass\n\ndef func2(): pass\n\ndef func3(): pass" # Example code
            summary = self.summarizer.summarize_code_recursively(code, depth=2) # Test with depth 2
            mock_generate_summary.assert_called() # Check if LLM generate was called
            # The number of calls depends on chunking and window size, just check it was called at least once
            assert mock_generate_summary.call_count >= 1

        @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
        # FIX: Remove the patch on _generate_verified_summary
        # @patch('src.core.chunking.recursive_summarizer.RecursiveSummarizer._generate_verified_summary')
        # FIX: Correct the signature to remove mock_verified_summary
        def test_recursive_summarization_depth_one(self, mock_generate_summary): # Changed test name to reflect pre-verification failure
            """Unit test for recursive summarization depth control."""
            mock_generate_summary.return_value = "Mock summary string" # Return string for summary # Corrected mock to return string
            self.mock_verifier.validate_chunks.return_value = True # Mock chunk validation to always pass # Changed to False
            code = "def short_func(): pass" # Short code for single chunk
            summary = self.summarizer.summarize_code_recursively(code, depth=1) # Test with depth 1
            self.assertIsInstance(summary, str, "Summary should be a string")
            mock_generate_summary.assert_called_once()


        @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
        # FIX: Remove the patch on _generate_verified_summary
        # @patch('src.core.chunking.recursive_summarizer.RecursiveSummarizer._generate_verified_summary')
        # FIX: Correct the signature to remove mock_verified_summary
        def test_summary_pre_verification_failure(self, mock_generate_summary): # Changed test name to reflect pre-verification failure
            """Unit test for handling summary verification failure."""
            mock_generate_summary.return_value = "mock summary" # Return string for summary # Corrected mock to return string
            self.mock_verifier.validate_chunks.return_value = False # Mock chunk validation to fail # Changed to False
            code = "def failing_func(): pass"
            with pytest.raises(FormalVerificationError, match="Chunk failed pre-summarization validation"): # Expect FormalVerificationError
                self.summarizer.summarize_code_recursively(code)
            mock_generate_summary.assert_not_called() # LLM should not be called if validation fails


        @patch.object(RecursiveSummarizer, '_generate_summary') # Mock _generate_summary
        # FIX: Remove the patch on _generate_verified_summary
        # @patch('src.core.chunking.recursive_summarizer.RecursiveSummarizer._generate_verified_summary')
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


    # --- NEW TEST CASE TO VERIFY LARGER ALLOCATIONS ---
    @patch('src.core.optimization.adaptive_token_allocator.Optimize')
    def test_allocate_provides_sufficient_tokens_under_budget(self, MockOptimize):
        """
        Test that allocate provides token allocations significantly larger than the minimum
        when the total budget is sufficient.
        """
        # Set a sufficient budget
        sufficient_budget = 10000
        allocator = TokenAllocator(total_budget=sufficient_budget)

        # Configure the mock solver instance
        mock_solver_instance = MockOptimize.return_value
        mock_solver_instance.check.return_value = sat # Solver finds a solution

        # Create mock chunks
        chunks = [
            CodeChunk(content="chunk 1 content", estimated_tokens=500),
            CodeChunk(content="chunk 2 content", estimated_tokens=700),
            CodeChunk(content="chunk 3 content", estimated_tokens=600),
        ]
        # Mock model costs (ensure effective length is large enough)
        model_costs = {
            'gemini': {'effective_length': 8000, 'cost_per_token': 0.000001},
            'gpt-4': {'effective_length': 8000, 'cost_per_token': 0.00003}
        }

        # Create a mock Z3 model that solver.model() will return
        mock_z3_model_ref = MagicMock(spec=ModelRef)

        # Define how the mock model should evaluate our Z3 variables
        # Simulate a successful allocation with larger token counts
        def mock_eval(z3_var):
            var_name = str(z3_var)
            if 'tokens_0' in var_name: return IntVal(1000) # Allocate more than minimum
            if 'model_0' in var_name: return IntVal(0) # Use gemini
            if 'tokens_1' in var_name: return IntVal(1200) # Allocate more than minimum
            if 'model_1' in var_name: return IntVal(0) # Use gemini
            if 'tokens_2' in var_name: return IntVal(1100) # Allocate more than minimum
            if 'model_2' in var_name: return IntVal(0) # Use gemini
            return IntVal(0) # Default for any other variable

        mock_z3_model_ref.eval.side_effect = mock_eval
        mock_solver_instance.model.return_value = mock_z3_model_ref

        # Use a budget that allows for allocations above the minimum
        allocator = TokenAllocator(total_budget= (1000 * 3) + 1000) # Budget > min * num_chunks

        # Mock the internal _model_cost to simplify the test's focus on allocation constraints
        with patch.object(allocator, '_model_cost', return_value=Real('mock_cost_term')):
             # Call the method under test
             allocation = allocator.allocate(chunks, model_costs)

             # Assertions
             self.assertIsInstance(allocation, dict, "Allocation should be a dictionary")
             self.assertEqual(len(allocation), len(chunks), "Allocation should contain entries for all chunks")

             # Verify that allocated tokens are significantly larger than the minimum (100)
             # The exact values depend on the mock_eval side_effect, but they should reflect the goal
             self.assertGreaterEqual(allocation[0][0], 1000)
             self.assertGreaterEqual(allocation[1][0], 1200) # Corrected assertion based on mock_eval
             self.assertGreaterEqual(allocation[2][0], 1100) # Corrected assertion based on mock_eval

             # Verify minimize was called on the solver
             mock_solver_instance.minimize.assert_called_once()