from src.core.agents.test_generator import TestGeneratorAgent

def test_test_generation():
    agent = TestGeneratorAgent()
    test_code = agent.generate_tests("def add(a,b): return a+b", {"functions": ["add"]})
    assert "def test_add_positive_numbers():" in test_code
    assert "def test_add_negative_numbers():" in test_code
    assert "def test_add_zero_values():" in test_code
    assert "def test_add_large_numbers():" in test_code
    assert "assert add(1, 2) == 3" in test_code
    assert "assert add(-2, -3) == -5" in test_code
    assert "assert add(0, 0) == 0" in test_code
    assert "assert add(1000000, 2000000) == 3000000" in test_code
