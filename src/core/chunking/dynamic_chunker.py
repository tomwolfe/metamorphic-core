# src/core/chunking/dynamic_chunker.py
import logging
from typing import List
from pydantic import BaseModel

logger = logging.getLogger(__name__)

class CodeChunk(BaseModel):
    """
    Represents a chunk of code with associated metadata for processing.
    """
    content: str
    estimated_tokens: int = 0
    id: str = None  # Example: chunk_1, chunk_2, etc.
    metadata: dict = {} # For additional info like line numbers, function names

class SemanticChunker:
    """
    Dynamically chunks code based on semantic understanding (placeholder for now).
    """
    def __init__(self):
        pass

    def chunk(self, code: str, max_tokens_per_chunk: int = 1500) -> List[CodeChunk]:
        """
        Placeholder for semantic chunking logic.
        For now, just splits code into simple chunks by lines, roughly respecting token limits.
        """
        lines = code.strip().splitlines()
        chunks = []
        current_chunk_lines = []
        current_token_count = 0
        chunk_counter = 1

        for line in lines:
            line_tokens = self._count_tokens(line) # Basic token count for now

            if current_token_count + line_tokens > max_tokens_per_chunk and current_chunk_lines:
                chunk_content = "\n".join(current_chunk_lines)
                chunks.append(CodeChunk(
                    content=chunk_content,
                    estimated_tokens=current_token_count,
                    id=f"chunk_{chunk_counter}"
                ))
                current_chunk_lines = [line] # Start new chunk with current line
                current_token_count = line_tokens
                chunk_counter += 1
            else:
                current_chunk_lines.append(line)
                current_token_count += line_tokens

        # Add any remaining lines as the last chunk
        if current_chunk_lines or not chunks: # Ensure at least one chunk even if input is empty
            chunk_content = "\n".join(current_chunk_lines)
            chunks.append(CodeChunk(
                content=chunk_content,
                estimated_tokens=current_token_count,
                id=f"chunk_{chunk_counter}"
            ))

        return chunks

    def _count_tokens(self, text: str) -> int:
        """
        Basic token counting - in real use, replace with a proper tokenizer.
        """
        return len(text.split()) # Simple word count approximation

if __name__ == '__main__':
    test_code = """
def function_one():
    print("This is function one.")

def function_two():
    print("This is function two, which is a bit longer.")

class MyClass:
    def __init__(self):
        self.attribute = "Initial value"

    def method_one(self):
        return "Method one output"

    def method_two(self, arg):
        if arg > 10:
            return "Large argument"
        else:
            return "Small argument"

# Some standalone code
x = 10
y = x * 2
print(f"Result: {y}")
"""
    chunker = SemanticChunker()
    code_chunks = chunker.chunk(test_code, max_tokens_per_chunk=200)

    for chunk in code_chunks:
        print(f"Chunk ID: {chunk.id}, Estimated Tokens: {chunk.estimated_tokens}")
        print("--- Chunk Content ---")
        print(chunk.content)
        print("\n" + "="*50 + "\n")
