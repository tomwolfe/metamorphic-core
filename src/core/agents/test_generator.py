from pydantic import UUID4
from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import KnowledgeGraph, Node
import os

class TestGenAgent:
    def __init__(self):
        self.llm = LLMOrchestrator()
        self.kg = KnowledgeGraph()

    def generate_tests(self, code: str, spec_analysis: dict) -> str:
        prompt = f"""
        Generate pytest tests for the Python function named {code}.
        The function is defined in the same file as the tests. Do not include any import statements.
        Include tests for Positive, Negative, Zero, and Large numbers.
        Return only pytest code with assertions, no explanations or comments/docstrings.
        """

        raw_response = self.llm.generate(prompt)

        # Even more robust code extraction:
        # 1. Look for ```python block specifically.
        # 2. Take the *first* code block found.
        # Robust code extraction: Check for markdown code blocks first.
        if "```python" in raw_response: # Check for the specific markdown block start
            test_code = raw_response.split("```python")[1].split("```")[0].strip() # Take content after ```python and before next ```
        else:
            # If no markdown, assume raw_response is already python code.
            test_code = raw_response.strip()

        test_code = self._store_tests(test_code, code_hash=hash(code))

        os.makedirs("generated_tests", exist_ok=True)


        # Define a placeholder function in the test file
        # Revised placeholder: now performs a basic identity operation, and includes a docstring.
        # In the future, this could be expanded to be context-aware based on spec_analysis.
        placeholder_function_def = f"""
def {code}(n=None):
    \"\"\"
    Placeholder function - intended to be dynamically generated.

    Currently, it raises a NotImplementedError to clearly indicate that it's a stub.
    In a future version, this function's implementation should be dynamically
    generated based on the 'spec_analysis' to provide more relevant and
     meaningful test cases.

    It also includes a print statement for basic logging when called during tests.
    \"\"\"
    print(f"Warning: Placeholder function '{{code}}' called. No real implementation yet.")
    raise NotImplementedError("Placeholder function - no real implementation provided.")

"""
        # Include the actual code, not a placeholder
        test_code_with_code = f"""
{placeholder_function_def}
{test_code}
        """.strip()

        with open("generated_tests/generated_tests.py", "w") as f:
            f.write(test_code_with_code)
        return test_code_with_code

        # Future enhancement:
        # - Use spec_analysis to guide the generation of more sophisticated
        #   placeholder function implementations and test cases.


    def _store_tests(self, test_code: str, code_hash: int) -> str:
        test_node = Node(type="generated_test", content=test_code, metadata={"source_hash": code_hash, "generator": "TestGeneratorAgent"})
        self.kg.add_node(test_node)
        return test_code # Add this line to return the test code
