import ast
import logging
from typing import List

logger = logging.getLogger(__name__)

class SemanticBoundaryDetector:
    """
    Detects semantic boundaries in Python code using AST parsing to guide chunking.
    """

    def detect_boundaries(self, code: str) -> List[int]:
        """
        Analyzes Python code and semantic boundaries for chunking.
        Returns a list of line numbers where boundaries are detected.
        """
        boundaries = []
        try:
            tree = ast.parse(code)
            for node in ast.walk(tree):
                if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
                    # Function and class definitions are strong semantic boundaries
                    boundaries.append(node.lineno)
                elif isinstance(node, ast.If):
                    # Consider 'if' blocks as potential boundaries
                    boundaries.append(node.lineno)
                elif isinstance(node, ast.For) or isinstance(node, ast.While):
                    # Loops can also be semantic boundaries
                    boundaries.append(node.lineno)
        except SyntaxError as e:
            logger.warning(f"Syntax error in code, boundary detection may be incomplete: {e}")
            # Fallback strategy: Split code into boundaries at each line break # Modified Fallback Strategy
            return list(range(1, len(code.splitlines()) + 1)) # Modified Fallback Strategy

        # Remove duplicate line numbers, sort them and ensure they are integers
        return sorted(list(set(boundaries)))
