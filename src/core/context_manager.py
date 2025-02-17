# src/core/context_manager.py
import ast
import io
import logging
from tokenize import tokenize, ENCODING, NEWLINE, NL, COMMENT, TokenInfo
from typing import List, Tuple, Optional
from pydantic import BaseModel
from src.core.knowledge_graph import KnowledgeGraph, Node, initialize_knowledge_graph

# Set up logging for error handling
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

class CodeChunk(BaseModel):
    content: str
    summary: str
    relationships: List[str] = []

def count_tokens(code_str: str) -> int:
    """
    Counts the number of meaningful tokens in a code string.
    Optimized for performance by using generator expressions.
    """
    try:
        buffer = io.BytesIO(code_str.encode('utf-8'))
        token_count = 0
        for token in tokenize(buffer.readline):
            if token.type not in (ENCODING, NEWLINE, NL, COMMENT):
                token_count += 1
        return token_count
    except Exception as e:
        logger.warning(f"Token counting error: {e}")
        return 0  # Treat as minimal token count

def parse_code_chunks(code: str, max_tokens: int = 1000) -> List[CodeChunk]:
    """
    Parses code into chunks with improved error handling and performance.
    """
    def parse_node(node):
        try:
            return ast.unparse(node).strip()
        except Exception as e:
            logger.warning(f"Failed to unparse node: {e}")
            return ""

    def get_token_count(node_code: str) -> int:
        return count_tokens(node_code)

    chunks = []
    current_chunk = []
    current_token_count = 0
    has_code_content_in_chunk = False

    # Early check: if code is empty or contains only comments, return no chunks
    stripped_code = code.strip()
    if not stripped_code or stripped_code.startswith('#') or stripped_code.startswith("'''") or stripped_code.startswith('"""'):
        return []

    try:
        tree = ast.parse(code)
    except SyntaxError as e:
        logger.error(f"Syntax error while parsing code: {e}")
        # Create a single chunk for unparsable code
        return [CodeChunk(
            content=code,
            summary=f"Code Chunk Summary: Unparsable code due to syntax error: {str(e)}"
        )]

    # Process each top-level node
    for node in ast.iter_child_nodes(tree):
        node_code = parse_node(node)
        if not node_code.strip() or node_code.strip().startswith('#') or node_code.strip().startswith("'''") or node_code.strip().startswith('"""'):
            continue # Skip if node is effectively empty or just a comment

        token_count = get_token_count(node_code)

        # Handle very long lines or large nodes
        if token_count == 0:
            continue

        if token_count < 100 and current_token_count + token_count <= max_tokens:
            current_chunk.append(node_code)
            current_token_count += token_count
            has_code_content_in_chunk = True
            continue

        if current_token_count + token_count > max_tokens and current_chunk:
            if has_code_content_in_chunk:
                chunks.append(CodeChunk(
                    content='\n\n'.join(current_chunk),
                    summary=generate_summary('\n\n'.join(current_chunk))
                ))
                has_code_content_in_chunk = False # Reset for the new chunk
            current_chunk = [node_code]
            current_token_count = token_count
            has_code_content_in_chunk = True
        else:
            current_chunk.append(node_code)
            current_token_count += token_count
            has_code_content_in_chunk = True

    # Cleanup any remaining code
    if current_chunk and has_code_content_in_chunk:
        chunks.append(CodeChunk(
            content='\n\n'.join(current_chunk),
            summary=generate_summary('\n\n'.join(current_chunk))
        ))

    return chunks

def generate_summary(code_chunk: str) -> str:
    summaries = []
    try:
        tree = ast.parse(code_chunk)
    except Exception as e:
        logger.warning(f"Failed to parse code for summary: {e}")
        return "Code Chunk Summary: Unable to parse code for summary"

    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            try:
                args = ', '.join(arg.arg for arg in node.args.args)
                summaries.append(f"Function: `{node.name}({args})`")
            except Exception as e:
                logger.warning(f"Error parsing function args: {e}")
        elif isinstance(node, ast.ClassDef):
            summaries.append(f"Class: `{node.name}`")

    return "; ".join(summaries) if summaries else "Code Chunk Summary: Miscellaneous code"

def integrate_chunks_into_kg(chunks: List[CodeChunk], kg: KnowledgeGraph):
    chunk_nodes = []
    for chunk in chunks:
        try:
            content_node = Node(type="code_chunk", content=chunk.content,
                               metadata={"summary": chunk.summary})
            content_node_id = kg.add_node(content_node)
            chunk_nodes.append(content_node_id)

            summary_node = Node(type="code_summary", content=chunk.summary,
                               metadata={"source_chunk_id": str(content_node_id)})
            summary_node_id = kg.add_node(summary_node)
            kg.add_edge(content_node_id, summary_node_id, "has_summary")
        except Exception as e:
            logger.error(f"Failed to integrate chunk into KG: {e}")

    try:
        for i in range(len(chunk_nodes) - 1):
            kg.add_edge(chunk_nodes[i], chunk_nodes[i+1], "precedes")
    except Exception as e:
        logger.error(f"Failed to add edges between chunks: {e}")

    return chunk_nodes

def _version_safe_unparse(node: ast.AST) -> str:
    """
    Attempts to safely unparse nodes with possible compatibility issues.
    """
    try:
        return ast.unparse(node)
    except Exception as e:
        logger.warning(f"Unparse error: {e}")
        return f"<UnparseError: {e}>" # Return an error string instead of using Placeholder

if __name__ == '__main__':
    # Test code remains similar with additional logging
    pass