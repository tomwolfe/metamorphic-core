from pydantic import UUID4
from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import KnowledgeGraph, Node
import os

class TestGenAgent:
    def __init__(self):
        self.llm = LLMOrchestrator()
        self.kg = KnowledgeGraph()

    def generate_tests(self, code: str, spec_analysis: dict) -> str:
        prompt = f"""Generate pytest tests for Python code: {code}.
        Include tests for: Positive, Negative, Zero, Large numbers.
        Return pytest code (assertions, no explanations, no comments/docstrings)."""

        raw_response = self.llm.generate(prompt)
        test_code = raw_response.split("`python")[-1].split("`")[0].strip()
        test_code = self._store_tests(test_code, code_hash=hash(code))

        os.makedirs("generated_tests", exist_ok=True)
        # Include the actual code, not a placeholder
        test_code_with_code = f"""
{code}
{test_code}
        """.strip()

        with open("generated_tests/generated_tests.py", "w") as f:
            f.write(test_code_with_code)
        return test_code_with_code

    def _store_tests(self, test_code: str, code_hash: int) -> str:
        test_node = Node(type="generated_test", content=test_code, metadata={"source_hash": code_hash, "generator": "TestGeneratorAgent"})
        self.kg.add_node(test_node)
        return test_code