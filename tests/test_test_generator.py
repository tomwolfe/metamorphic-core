# File: tests/test_test_generator.py
from src.core.agents.test_generator import TestGenerationAgent
from unittest.mock import patch

@patch('src.core.llm_orchestration.LLMOrchestrator.generate')
def test_test_generation(mock_generate):
    mock_response = """import pytest
    
    def test_add_positive_numbers():
        assert add(1, 2) == 3
    
    def test_add_negative_numbers():
        assert add(-1, -2) == -3
    
    def test_add_zero_values():
        assert add(0, 0) == 0
    
    def test_add_large_numbers():
        assert add(1000000, 2000000) == 3000000
    """
    mock_generate.return_value = mock_response
    
    agent = TestGenerationAgent()
    test_code = agent.generate_tests("def add(a,b): return a+b", {"functions": ["add"]})
    
    assert "def test_add_positive_numbers():" in test_code
    assert "def test_add_negative_numbers():" in test_code 
    assert "def test_add_zero_values():" in test_code
    assert "def test_add_large_numbers():" in test_code
    assert "assert add(1, 2) == 3" in test_code
    assert "assert add(-1, -2) == -3" in test_code
    assert "assert add(0, 0) == 0" in test_code
    assert "assert add(1000000, 2000000) == 3000000" in test_code
