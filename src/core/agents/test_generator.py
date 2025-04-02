# src/core/agents/test_generator.py
import re
from pydantic import UUID4
from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import KnowledgeGraph, Node
import os

class TestGeneratorAgent: # Renamed class
    def __init__(self):
        self.llm = LLMOrchestrator()
        self.kg = KnowledgeGraph()

    def generate_tests(self, code: str, spec_analysis: dict,
                      file_path: str = "generated_tests/generated_tests.py") -> str: # Modified - added file_path with default
        """
        Generate placeholder pytest tests for a function and write them to a file.

        Args:
            code: The Python code to test (e.g., function definition).
            spec_analysis: (Future use) Metadata about code requirements.
            file_path: Path to save generated test code (default: generated_tests/generated_tests.py).
        """
        # function_name = self._extract_function_name(code)  # Leverage existing helper
        function_name = "placeholder_function" # Hardcode a placeholder function name for MVP simplicity

        test_code = f"""import pytest

def test_{function_name}_positive():
    pytest.skip("Placeholder test: Positive case")
    assert True

def test_{function_name}_negative():
    pytest.skip("Placeholder test: Negative case")
    assert True
"""

        # Create directory if it doesn't exist
        os.makedirs(os.path.dirname(file_path), exist_ok=True)

        # Write the generated tests to file
        with open(file_path, 'w') as f:
            f.write(test_code)

        return test_code

    ''' # ------------------------ COMMENT BLOCK START --------------------------
    # Commenting out _extract_function_name and _store_tests for Phase 1 MVP Simplification
    # These methods might be re-enabled or their logic reused in Phase 2 or Phase 3 for enhanced
    # test generation and Knowledge Graph integration.
    # Note: Using raw string r'' for regex below to avoid escape sequence warnings.
    def _extract_function_name(self, code: str) -> str:
        """Helper to extract function name from code string."""
        match = re.search(r'^def (\w+)', code, re.MULTILINE) # Using raw string r''
        return match.group(1) if match else "unknown_function"

    def _store_tests(self, test_code: str, code_hash: int) -> str:
        import pytest  # Import pytest here to make it available in the generated code

        modified_test_code_lines = []
        modified_test_code_lines.append("import pytest\\n") # Add import pytest with newline

        for line in test_code.splitlines():
            if line.strip().startswith("def test_"): # Identify test functions
                modified_test_code_lines.append(line)
                modified_test_code_lines.append(f"    pytest.skip(\\"Placeholder test - function implementation pending\\")") # Add skip
            else:
                modified_test_code_lines.append(line)

        modified_test_code = "\\n".join(modified_test_code_lines)

        test_node = Node(
            type="generated_test",
            content=modified_test_code,
            metadata={"source_hash": code_hash, "generator": "TestGeneratorAgent"} # Updated generator name metadata
        )
        self.kg.add_node(test_node)
        return modified_test_code
    ''' # ------------------------ COMMENT BLOCK END --------------------------
