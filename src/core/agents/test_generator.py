import re
from pydantic import UUID4
from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import KnowledgeGraph, Node
import os

class TestGenAgent:
    def __init__(self):
        self.llm = LLMOrchestrator()
        self.kg = KnowledgeGraph()

    def generate_tests(self, code: str, spec_analysis: dict) -> str:
        function_name = self._extract_function_name(code)

        # Revised prompt to request skippable tests
        prompt = f"""
Given the following Python function:
{code}

Generate pytest tests for this function as placeholders that are skipped.
- Do NOT include the function code itself in your response.
- Tests must cover positive, negative, zero, and large numbers.
- Generate pytest tests that are marked to be skipped using pytest.skip().
- Only return the test code (no explanations or other text).
- Include the 'pytest' import at the beginning of the test file.
"""

        raw_response = self.llm.generate(prompt)
        # Extract code block properly
        if "```python" in raw_response:
            test_code = raw_response.split("```python")[1].split("```")[0].strip()
        else:
            test_code = raw_response.strip()

        test_code = self._store_tests(test_code, code_hash=hash(code))
        os.makedirs("generated_tests", exist_ok=True)

        # Create placeholder function
        placeholder_function_def = f"""
def {function_name}(n=None):
    \"\"\"Placeholder function. Raises NotImplementedError.\"\"\"
    print(f"Warning: Placeholder '{function_name}' called.")
    raise NotImplementedError("No implementation yet.")
"""

        test_code_with_code = f"""{placeholder_function_def}\n{test_code}""".strip()

        with open("generated_tests/generated_tests.py", "w") as f:
            f.write(test_code_with_code)
        return test_code_with_code

    def _extract_function_name(self, code: str) -> str:
        match = re.search(r'^def (\w+)', code, re.MULTILINE)
        return match.group(1) if match else "unknown_function"

    def _store_tests(self, test_code: str, code_hash: int) -> str:
        import pytest  # Import pytest here to make it available in the generated code

        modified_test_code_lines = []
        modified_test_code_lines.append("import pytest") # Add import pytest at the beginning

        for line in test_code.splitlines():
            if line.strip().startswith("def test_"): # Identify test functions
                modified_test_code_lines.append(line)
                modified_test_code_lines.append(f"    pytest.skip(\"Placeholder test - function implementation pending\")") # Add skip
            else:
                modified_test_code_lines.append(line)

        modified_test_code = "\n".join(modified_test_code_lines)

        test_node = Node(
            type="generated_test",
            content=modified_test_code,
            metadata={"source_hash": code_hash, "generator": "TestGeneratorAgent"}
        )
        self.kg.add_node(test_node)
        return modified_test_code
