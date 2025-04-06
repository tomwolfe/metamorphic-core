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
        function_name = self._extract_function_name(code)  # Leverage existing helper

        # Attempt to generate a basic positive test case
        positive_test_assertion = self._generate_basic_positive_assertion(code, function_name)

        if positive_test_assertion:  # If a positive test could be generated
            test_code = f"""import pytest

def test_{function_name}_positive(): # Corrected test function names to use function_name
    {positive_test_assertion}

def test_{function_name}_negative():
    pytest.skip(f"Placeholder test: Negative case for function '{function_name}'") # Corrected skip message
    assert True
""" # Corrected f-string and formatting
        else:  # Fallback to placeholder tests if positive test generation fails
            test_code = f"""import pytest

def test_{function_name}_positive():
    pytest.skip(f"Placeholder test: Positive case for function '{function_name}'")
    assert True

def test_{function_name}_negative():
    pytest.skip(f"Placeholder test: Negative case for function '{function_name}'")
    assert True
""" # Corrected f-string and formatting

        # Create directory if it doesn't exist
        os.makedirs(os.path.dirname(file_path), exist_ok=True)

        # Write the generated tests to file
        with open(file_path, 'w') as f:
            f.write(test_code)

        # Store tests in KG - Re-integrated
        self._store_tests(test_code, hash(code)) # Call _store_tests to store in KG

        return test_code

    def _generate_basic_positive_assertion(self, code: str, function_name: str) -> str:
        """
        Generates a more dynamic positive test assertion by attempting basic type inference.
        Focuses on numerical functions for this MVP iteration.
        """
        try:
            import ast
            tree = ast.parse(code)
            function_def = None
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef) and node.name == function_name:
                    function_def = node
                    break

            if not function_def:
                return None  # Function definition not found (shouldn't happen, but defensive)

            # Very basic parameter type inference - MVP level
            argument_names = [arg.arg for arg in function_def.args.args]
            if not argument_names:
                return None # No arguments, can't generate numerical test easily

            # Heuristic: Assume numerical if no type hints or simple names
            is_numerical_input = True # Assume numerical for simplicity in MVP

            if is_numerical_input:
                input_values = []
                if len(argument_names) == 1:
                    input_values = [2] # Single input example
                elif len(argument_names) == 2:
                    input_values = [3, 5] # Two input example
                else:
                    return None # More than 2 args, skip for now

                # Extremely basic output prediction for MVP - only addition, squaring, and multiplication
                if "square" in function_name.lower():
                    expected_output = input_values[0] * input_values[0] if input_values else None
                elif "add" in function_name.lower():
                    expected_output = sum(input_values) if input_values else None
                elif "multiply" in function_name.lower(): # ADDED: Handle "multiply"
                    expected_output = input_values[0] * input_values[1] if len(input_values) == 2 else None # For 2-arg multiply
                else: # Fallback - try simple addition if two inputs
                    expected_output = sum(input_values) if len(input_values) == 2 else None


                if expected_output is not None:
                    arg_str = ', '.join(map(str, input_values)) # Format input values
                    return f"assert {function_name}({arg_str}) == {expected_output}"

        except SyntaxError:
            return None # Code parsing error, fallback
        except Exception as e: # Catch-all for robustness in basic implementation
            import logging
            logging.error(f"Error during dynamic assertion generation: {e}")
            return None # Error during assertion generation, fallback

        return None # Fallback to None if no dynamic assertion could be created

    # _extract_function_name and _store_tests RE-INTEGRATED - COMMENT BLOCK REMOVED
    def _extract_function_name(self, code: str) -> str:
        """Helper to extract function name from code string."""
        match = re.search(r'^def (\w+)', code, re.MULTILINE) # ENSURE raw string r'' HERE
        return match.group(1) if match else "unknown_function"

    def _store_tests(self, test_code: str, code_hash: int) -> str:
        import pytest  # Import pytest here to make it available in the generated code

        modified_test_code_lines = []
        modified_test_code_lines.append("import pytest\\n") # Add import pytest with newline

        for line in test_code.splitlines():
            if line.strip().startswith("def test_"): # Identify test functions
                modified_test_code_lines.append(line)
                modified_test_code_lines.append(f'    pytest.skip("Placeholder test - function implementation pending")') # Add skip # --- CORRECTED LINE HERE ---
            else:
                modified_test_code_lines.append(line)

        modified_test_code = "\\n".join(modified_test_code_lines)

        test_node = Node(
            type="generated_test",
            content=modified_test_code,
            metadata={"source_hash": code_hash, "generator": "TestGeneratorAgent"} # Updated generator name metadata
        )