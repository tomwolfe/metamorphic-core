# src/core/context_manager.py
import ast
import io
from tokenize import tokenize, ENCODING, NEWLINE, NL, COMMENT
from typing import List, Tuple
from pydantic import BaseModel
from src.core.knowledge_graph import KnowledgeGraph, Node, initialize_knowledge_graph # Assuming knowledge_graph.py is in src/core

class CodeChunk(BaseModel):
    content: str
    summary: str
    relationships: List[str] = []

def count_tokens(code_str: str) -> int:
    """
    Counts the number of meaningful tokens in a code string.
    """
    buffer = io.BytesIO(code_str.encode('utf-8'))
    counter = 0
    for token in tokenize(buffer.readline):
        if token.type not in ( ENCODING, NEWLINE, NL, COMMENT ):
            counter += 1
    return counter

def parse_code_chunks(code: str) -> List[CodeChunk]:
    try:
        tree = ast.parse(code)
    except SyntaxError as e:
        return [CodeChunk(content=code, summary=f"Code Chunk Summary: Unable to parse code due to syntax error: {e}")]

    chunks = []
    current_chunk = []
    current_token_count = 0
    MAX_TOKENS = 1000  # Lowered from 1500 for better chunk sizing

    # Process each top-level node
    for node in ast.iter_child_nodes(tree):
        node_code = ast.unparse(node).strip()
        token_count = count_tokens(node_code)

        # For small chunks (under 100 tokens), combine them
        if token_count < 100 and current_token_count + token_count <= MAX_TOKENS:
            current_chunk.append(node_code)
            current_token_count += token_count
            continue

        # For larger chunks, check if we need to start a new one
        if current_token_count + token_count > MAX_TOKENS and current_chunk:
            chunks.append(CodeChunk(
                content='\n\n'.join(current_chunk),
                summary=generate_summary('\n\n'.join(current_chunk))
            ))
            current_chunk = []
            current_token_count = 0

        current_chunk.append(node_code)
        current_token_count += token_count

    # Add any remaining context chunk
    if current_chunk:
        chunks.append(CodeChunk(
            content='\n\n'.join(current_chunk),
            summary=generate_summary('\n\n'.join(current_chunk))
        ))

    return chunks

def generate_summary(code_chunk: str) -> str:
    summaries = []
    try:
        tree = ast.parse(code_chunk)
    except Exception:
        return "Code Chunk Summary: Unable to parse code."

    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            args = ', '.join(arg.arg for arg in node.args.args)
            summaries.append(f"Function: `{node.name}({args})`")
        elif isinstance(node, ast.ClassDef):
            summaries.append(f"Class: `{node.name}`")

    return "; ".join(summaries) if summaries else "Code Chunk Summary: Miscellaneous code."

def integrate_chunks_into_kg(chunks: List[CodeChunk], kg: KnowledgeGraph):
    """
    Integrates code chunks into the knowledge graph.
    """
    chunk_nodes = []
    for chunk in chunks:
        content_node = Node(type="code_chunk", content=chunk.content, metadata={"summary": chunk.summary})
        content_node_id = kg.add_node(content_node)
        chunk_nodes.append(content_node_id)

        summary_node = Node(type="code_summary", content=chunk.summary, metadata={"source_chunk_id": str(content_node_id)})
        summary_node_id = kg.add_node(summary_node)
        kg.add_edge(content_node_id, summary_node_id, "has_summary")

    for i in range(len(chunk_nodes) - 1): # Simple linear chain for now
        kg.add_edge(chunk_nodes[i], chunk_nodes[i+1], "precedes")

    return chunk_nodes


if __name__ == '__main__':
    code_example = """
def hello_world():
    print("Hello, world!")

class MyClass:
    def __init__(self, name):
        self.name = name

    def greet(self):
        return f"Hello, {self.name}!"

def another_function(x, y):
    return x + y

# Some comments and extra code to make it longer
# Line 1
# Line 2
# Line 3
# Line 4
# Line 5
# Line 6
# Line 7
# Line 8
# Line 9
# Line 10
"""
    chunks = parse_code_chunks(code_example)
    for i, chunk in enumerate(chunks):
        print(f"Chunk {i+1} Summary: {chunk.summary}")
        print(f"Chunk {i+1} Content:\n{chunk.content}\n---")

    kg = initialize_knowledge_graph()
    chunk_node_ids = integrate_chunks_into_kg(chunks, kg)
    print("\nKnowledge Graph Integration completed.")
    for node_id in chunk_node_ids:
        node = kg.get_node(node_id)
        print(f"Node ID: {node_id}, Type: {node.type}, Summary: {node.metadata.get('summary')[:50]}...") # Print first 50 chars of summary