from pydantic import UUID4
from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import KnowledgeGraph, Node
import os

class TestGenAgent:
    def __init__(self):
        self.llm = LLMOrchestrator()
        self.kg = KnowledgeGraph()

    def generate_tests(self, code: str, spec_analysis: dict) -> str:
        prompt = f"""Generate pytest tests for this Python code:
        {code}
        
        Include tests for these cases:
        - Positive numbers
        - Negative numbers
        - Zero values
        - Large numbers
        
        Return only valid pytest code with assertions, no explanations. Do not include any comments or docstrings in the test code."""

        raw_response = self.llm.generate(prompt)
        # Extract test code from LLM response (handle markdown formatting)
        test_code = raw_response.split("```python")[-1].split("```")[0].strip()
        test_code = self._store_tests(test_code, code_hash=hash(code))

        os.makedirs("generated_tests", exist_ok=True)
        test_code_with_placeholder = f"""
def placeholder_code(n):
    return n
{test_code}
        """.strip()  # Remove leading/trailing whitespace

        with open("generated_tests/generated_tests.py", "w") as f:
            f.write(test_code_with_placeholder)

        return test_code_with_placeholder  # Return full content (placeholder + tests)

    def _store_tests(self, test_code: str, code_hash: int) -> str:
        test_node = Node(
            type="generated_test",
            content=test_code,
            metadata={
                "source_hash": code_hash,
                "generator": "TestGeneratorAgent"
            }
        )
        self.kg.add_node(test_node)
        return test_code