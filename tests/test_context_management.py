# tests/test_context_management.py
import unittest
from src.core.context_manager import parse_code_chunks, generate_summary, integrate_chunks_into_kg, CodeChunk
from src.core.knowledge_graph import KnowledgeGraph, initialize_knowledge_graph

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

if __name__ == '__main__':
    unittest.main()
