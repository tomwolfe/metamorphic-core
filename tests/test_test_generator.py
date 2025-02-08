from src.core.agents.test_generator import TestGeneratorAgent

def test_test_generation():
    agent = TestGeneratorAgent()
    test_code = agent.generate_tests("def add(a,b): return a+b", {"functions": ["add"]})
    assert "def test_add():" in test_code
    assert "assert add(2,3) == 5" in test_code
