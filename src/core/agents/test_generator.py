from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import KnowledgeGraph, Node

class TestGeneratorAgent:
    def __init__(self):
        self.llm = LLMOrchestrator()
        self.kg = KnowledgeGraph()

    def generate_tests(self, code: str, spec_analysis: dict) -> dict:
        prompt = f"""Generate pytest tests for this Python code:
        {code}
        
        Code analysis: {spec_analysis}
        Return only valid pytest code with assertions."""
        
        response = self.llm.generate(prompt)
        return self._store_tests(response, code_hash=hash(code))

    def _store_tests(self, test_code: str, code_hash: int) -> dict:
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
