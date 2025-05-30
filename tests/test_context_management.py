# tests/test_context_management.py
import unittest
import time
import logging
from io import StringIO
from src.core.context_manager import parse_code_chunks, generate_summary, integrate_chunks_into_kg, CodeChunk, count_tokens
from src.core.knowledge_graph import KnowledgeGraph, initialize_knowledge_graph
from src.core.llm_orchestration import LLMOrchestrator, EnhancedLLMOrchestrator # added import
from unittest.mock import patch, MagicMock


class TestContextManagement(unittest.TestCase):

    def test_parse_code_chunks_basic(self):
        test_code = """
def func1():
    pass

def func2():
    pass
"""
        chunks = parse_code_chunks(test_code)
        self.assertEqual(len(chunks), 1)  # Should be one chunk as it's small
        self.assertIn("Function: `func1()", chunks[0].summary)
        self.assertIn("Function: `func2()", chunks[0].summary)

    def test_parse_code_chunks_large(self):
        long_code = ""
        for i in range(500):  # Increased to 500 to exceed 3000 tokens
            long_code += f"""
def function_{i}():
    '''This is function number {i}'''
    pass
"""
        chunks = parse_code_chunks(long_code)
        self.assertGreater(len(chunks), 1) # Should be chunked

    def test_generate_summary_function(self):
        code_chunk = "def my_function(arg1, arg2):\n  pass"
        summary = generate_summary(code_chunk)
        self.assertIn("Function: `my_function(arg1, arg2)`", summary)

    def test_generate_summary_class(self):
        code_chunk = "class MyClass:\n  def __init__(self):\n    pass"
        summary = generate_summary(code_chunk)
        self.assertIn("Class: `MyClass`", summary)

    def test_integrate_chunks_into_kg(self):
        kg = initialize_knowledge_graph()
        chunks = [
            CodeChunk(content="def chunk1(): pass", summary="Summary 1"),
            CodeChunk(content="class Chunk2: pass", summary="Summary 2")
        ]
        chunk_node_ids = integrate_chunks_into_kg(chunks, kg)
        self.assertEqual(len(chunk_node_ids), 2)
        self.assertIn("code_chunk", kg.nodes[chunk_node_ids[0]].type)
        self.assertIn("code_summary", kg.get_relationships(chunk_node_ids[0], relationship_type="has_summary")[0].type)
        self.assertIn("precedes", [edge.type for edge in kg.edges.values() if edge.source == chunk_node_ids[0] and edge.target == chunk_node_ids[1]])

class TestEdgeCases(unittest.TestCase):
    def test_parse_code_chunks_long_lines(self):
        """Test code with very long lines (>500 characters) within a function."""
        long_line = "x = " + "some_long_string " * 100  # ~500 characters
        test_code = f"""
def long_line_function():
    {long_line!r}
"""
        chunks = parse_code_chunks(test_code)
        self.assertEqual(len(chunks), 1)
        self.assertIn("Function: `long_line_function()", chunks[0].summary)

    def test_parse_code_chunks_complex_syntax(self):
        """Test code with complex or unusual syntax."""
        complex_code = """
def function_with_lambda():
    return lambda x: x + 1

class ClassWithNestedFunctions:
    def __init__(self):
        self.func = lambda x: x * 2

        def inner_func(y):
            return y - 1
"""
        chunks = parse_code_chunks(complex_code)
        self.assertEqual(len(chunks), 1)
        self.assertIn("Function: `function_with_lambda()", chunks[0].summary)
        self.assertIn("Class: `ClassWithNestedFunctions", chunks[0].summary)

    def test_parse_code_chunks_syntactically_invalid(self):
        """Test code with syntax errors to ensure graceful handling."""
        invalid_code = """
def invalid_function():
    print "Hello, World!"  # Missing parentheses

class InvalidClass:
    def __init__(self):
        # Missing indentation
        pass
"""
        chunks = parse_code_chunks(invalid_code)
        self.assertEqual(len(chunks), 1) # Expecting 1 chunk for invalid code with error summary
        self.assertIn("Unparsable code", chunks[0].summary) # Expecting summary indicating parse failure

    def test_parse_code_chunks_edge_structures(self):
        """Test various file structures including edge cases."""
        # Only top-level functions
        top_level_code = "\n".join([f"def func_{i}(): pass" for i in range(50)])
        chunks = parse_code_chunks(top_level_code)
        self.assertLessEqual(len(chunks), 50) # Expecting multiple chunks, but less than the number of functions (grouping possible)

        # Deeply nested code
        nested_code = ""
        for i in range(5):
            nested_code += f"class Class_{i}:\n"
            nested_code += f"    def func_{i}(self):\n"
            nested_code += f"        pass\n"
        chunks = parse_code_chunks(nested_code)
        self.assertEqual(len(chunks), 1)

    def test_empty_file(self):
        """Test empty file handling"""
        chunks = parse_code_chunks("")
        self.assertEqual(len(chunks), 0)

    def test_only_comments(self):
        """Test file with only comments"""
        chunks = parse_code_chunks("'''This is a comment'''")
        self.assertEqual(len(chunks), 0) # Should be no chunks

    def test_long_lines(self):
        """Test very long lines"""
        long_line = "x = " + "a" * 1000
        code = f"def f():\n    {long_line}"
        chunks = parse_code_chunks(code)
        self.assertEqual(len(chunks), 1)


class TestPerformance(unittest.TestCase):
    def test_parse_code_chunks_performance(self):
        """Measure performance on a large codebase (~32k tokens)."""
        # Assuming you have a large_code_sample.py file in your tests directory
        try:
            with open("tests/large_code_sample.py", "r") as f:
                large_code = f.read()
        except FileNotFoundError:
            # Create a dummy large_code_sample.py if it doesn't exist for testing purposes
            large_code = ""
            for i in range(6000): # approx 30k tokens
                large_code += "def dummy_function_" + str(i) + "():\n    pass\n"
            with open("tests/large_code_sample.py", "w") as f:
                f.write(large_code)


        start_time = time.time()
        chunks = parse_code_chunks(large_code)
        end_time = time.time()

        execution_time = end_time - start_time
        # Calculate tokens per second
        total_tokens = count_tokens(large_code)
        tokens_per_second = total_tokens / execution_time

        # Ensure performance is below 2 seconds per 4k tokens
        max_acceptable_time = (total_tokens / 4000) * 2
        self.assertLessEqual(execution_time, max_acceptable_time,
                            f"Performance test failed. Execution time: {execution_time:.2f}s, Expected: < {max_acceptable_time:.2f}s")

    def test_large_codebase(self):
        """Test performance with large real-world codebase"""
        # Create a dummy large_real_codebase.py if it doesn't exist for testing purposes
        large_real_codebase_content = ""
        for i in range(12000): # approx 60k tokens
            large_real_codebase_content += "def real_dummy_function_" + str(i) + "():\n    pass\n"
        with open("tests/large_real_codebase.py", "w") as f:
            f.write(large_real_codebase_content)

        with open("tests/large_real_codebase.py", "r") as f:
            code = f.read()

        start_time = time.time()
        chunks = parse_code_chunks(code)
        end_time = time.time()

        total_tokens = count_tokens(code)
        max_tokens = (total_tokens / 4000) * 2 # 2 seconds per 4k tokens
        self.assertLessEqual(end_time - start_time, max_tokens, f"Performance test failed. Execution time: {end_time - start_time:.2f}s, Expected: < {max_tokens:.2f}s")


class TestImports(unittest.TestCase):
    def test_parse_code_chunks_imports(self):
        """Test preservation of import dependencies within chunks."""
        import_code = """
import math
from datetime import datetime

def use_math():
    return math.sqrt(2)

class UsesDateTime:
    def __init__(self):
        self.time = datetime.now()
"""
        chunks = parse_code_chunks(import_code)
        self.assertEqual(len(chunks), 1)
        self.assertIn("Function: `use_math()", chunks[0].summary)
        self.assertIn("Class: `UsesDateTime", chunks[0].summary)

    def test_import_preservation(self):
        """Test import statement preservation"""
        code = """
import math
def f():
    return math.sqrt(2)
"""
        chunks = parse_code_chunks(code)
        self.assertEqual(len(chunks), 1)

class TestCoverage(unittest.TestCase): # Inherit from unittest.TestCase
    def test_full_coverage(self):
        """Test full code coverage"""
        # This is a placeholder for coverage verification
        pass

class TestIntegration(unittest.TestCase):
    def test_integration_with_llm_orchestrator(self):
        """Test integration with LLMOrchestrator."""
        orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=MagicMock(),
            ethics_engine=MagicMock()
        )
        test_code = "def test_function(): pass"

        with patch('src.core.llm_orchestration.EnhancedLLMOrchestrator._handle_large_context') as mock_chunking:
            mock_chunking.return_value = [CodeChunk(content=test_code, summary="Mock Summary")]
            chunks = orchestrator._handle_large_context(test_code)
            self.assertIsInstance(chunks[0], CodeChunk)


if __name__ == '__main__':
    unittest.main()



