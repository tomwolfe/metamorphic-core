# File: src/core/agents/test_generator.py
from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import KnowledgeGraph, Node # Add Node import

class TestGeneratorAgent:
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

        Return only valid pytest code with assertions, no explanations."""

        raw_response = self.llm.generate(prompt)
        # Clean markdown formatting
        test_code = raw_response.split("```python")[-1].split("```")[0].strip()
        return self._store_tests(test_code, code_hash=hash(code))

    def _store_tests(self, test_code: str, code_hash: int) -> str:
        test_node = Node( # Changed to Node instantiation
            type="generated_test",
            content=test_code,
            metadata={
                "source_hash": code_hash,
                "generator": "TestGeneratorAgent"
            }
        )
        self.kg.add_node(test_node)
        return test_code
