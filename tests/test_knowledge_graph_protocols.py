"""
Unit tests for the multi-stage code generation protocol in KnowledgeGraph.
"""

import pytest
from src.core.llm.knowledge_graph import KnowledgeGraphWithMultiStageCodeGen


@pytest.fixture
def kg_protocol_agent():
    """Provides an instance of the KnowledgeGraphWithMultiStageCodeGen."""
    return KnowledgeGraphWithMultiStageCodeGen()


def test_generate_test_method_skeleton(kg_protocol_agent):
    """Verify generation of a basic test method skeleton."""
    skeleton = kg_protocol_agent.generate_test_method_skeleton(
        "test_add_numbers", "add_numbers"
    )
    assert "def test_add_numbers(test_input, expected_output):" in skeleton
    assert '"""Test the add_numbers function."""' in skeleton
    assert "    pass" in skeleton


def test_generate_individual_test_cases(kg_protocol_agent):
    """Verify generation of the formatted string for test cases."""
    test_cases = [
        {"inputs": {"a": 1, "b": 2}, "expected": 3},
        {"inputs": {"a": -1, "b": 1}, "expected": 0},
    ]
    cases_str = kg_protocol_agent.generate_individual_test_cases(test_cases)
    assert "({'a': 1, 'b': 2}, 3)" in cases_str
    assert "({'a': -1, 'b': 1}, 0)" in cases_str
    assert cases_str.strip().startswith("[")
    assert cases_str.strip().endswith("]")


def test_add_parametrize_decorator(kg_protocol_agent):
    """Verify adding the parametrize decorator to the skeleton."""
    skeleton = "def test_add(i, o):\n    pass"
    cases_str = "[({'a': 1}, 1)]"
    decorated_code = kg_protocol_agent.add_parametrize_decorator(skeleton, cases_str)

    assert "@pytest.mark.parametrize" in decorated_code
    assert '"test_input, expected_output"' in decorated_code
    assert "[({'a': 1}, 1)]" in decorated_code
    assert decorated_code.endswith(skeleton)


def test_add_validation_logic_ast(kg_protocol_agent):
    """Verify replacing the 'pass' statement with assertion logic via AST."""
    code_with_pass = (
        "def test_add_numbers(test_input, expected_output):\n"
        '    """Test the add_numbers function."""\n'
        "    pass"
    )
    final_code = kg_protocol_agent.add_validation_logic(
        code_with_pass, "add_numbers"
    )
    assert "pass" not in final_code
    # ast.unparse might format slightly differently, so check for key elements
    assert "assert add_numbers(**test_input) == expected_output".replace(" ", "") in final_code.replace(" ", "")


def test_full_protocol_integration(kg_protocol_agent):
    """Verify the full multi-stage protocol integration."""
    test_cases = [{"inputs": {"a": 5, "b": 5}, "expected": 10}]
    # Stage 1
    skeleton = kg_protocol_agent.generate_test_method_skeleton("test_add", "add")
    # Stage 3
    cases_str = kg_protocol_agent.generate_individual_test_cases(test_cases)
    # Stage 2
    decorated = kg_protocol_agent.add_parametrize_decorator(skeleton, cases_str)
    # Stage 4
    final_code = kg_protocol_agent.add_validation_logic(decorated, "add")

    assert "@pytest.mark.parametrize" in final_code
    assert "({'a': 5, 'b': 5}, 10)" in final_code
    assert "assert add(**test_input) == expected_output" in final_code