"""
This module extends the KnowledgeGraph with specialized protocols for robust,
multi-stage code generation, particularly for creating test cases.
"""
import ast
import logging
from typing import List, Dict, Any

from pydantic import PrivateAttr

from src.core.knowledge_graph import KnowledgeGraph as BaseKnowledgeGraph


class _PassReplacer(ast.NodeTransformer):
    """An AST transformer to replace a Pass node with an Assert node."""
    def __init__(self, function_name: str):
        self.function_name = function_name
        self.replaced = False

    def visit_Pass(self, node: ast.Pass) -> Any:
        if self.replaced:
            return node
        self.replaced = True
        # Construct the assertion: assert function_name(**test_input) == expected_output
        assert_node = ast.Assert(
            test=ast.Compare(
                left=ast.Call(
                    func=ast.Name(id=self.function_name, ctx=ast.Load()),
                    args=[],
                    keywords=[ast.keyword(arg=None, value=ast.Name(id='test_input', ctx=ast.Load()))]
                ),
                ops=[ast.Eq()],
                comparators=[ast.Name(id='expected_output', ctx=ast.Load())]
            ),
            msg=None
        )
        # Return the new Assert node to replace the Pass node
        return ast.copy_location(assert_node, node)


class KnowledgeGraphWithMultiStageCodeGen(BaseKnowledgeGraph):
    """
    Extends the KnowledgeGraph with a protocol for multi-stage code generation
    to improve reliability and isolate failure points.
    """
    # Declare _logger as a private attribute with a string literal type hint to avoid
    # 'TypeError: 'function' object is not subscriptable' during pytest collection.
    _logger: logging.Logger = PrivateAttr(default_factory=lambda: logging.getLogger(__name__))

    def __init__(self, logger: logging.Logger = None):
        """
        Initializes the KnowledgeGraphWithMultiStageCodeGen.

        Args:
            logger: An optional logger instance.
        """
        super().__init__() # Call BaseModel's __init__
        self._logger = logger or logging.getLogger(__name__) # Assign to private attribute

    def generate_test_method_skeleton(
        self, test_method_name: str, function_to_test_name: str
    ) -> str:
        """
        Generates a basic Python test function skeleton.

        Args:
            test_method_name: The name for the new test method.
            function_to_test_name: The name of the function being tested.

        Returns:
            A string containing the test function skeleton.
        """
        return (
            f"def {test_method_name}(test_input, expected_output):\n"
            f'    """Test the {function_to_test_name} function."""\n'
            f"    pass\n"
        )

    def add_parametrize_decorator(
        self, test_code: str, test_cases_str: str
    ) -> str:
        """ 
        Adds the @pytest.mark.parametrize decorator to a test function string.

        Args:
            test_code: The string containing the test function definition.
            test_cases_str: The string representation of the test cases list.

        Returns:
            The test code with the decorator added.
        """
        decorator = (
            '@pytest.mark.parametrize(\n'
            '    "test_input, expected_output",\n'
            f'    {test_cases_str}\n'
            ')'
        )
        return f"{decorator}\n{test_code}"

    def generate_individual_test_cases(
        self, test_cases: List[Dict[str, Any]]
    ) -> str:
        """
        Generates a formatted string for test cases for the parametrize decorator.

        Args:
            test_cases: A list of dictionaries, each with 'inputs' and 'expected'.

        Returns:
            A formatted string of the test case data.
        """
        return "[\n" + ",\n".join(
            f"        ({repr(case['inputs'])}, {repr(case['expected'])})"
            for case in test_cases
        ) + "\n    ]"

    def add_validation_logic(self, test_code: str, function_to_test_name: str) -> str:
        """Replaces 'pass' with the actual test validation logic using AST."""
        try:
            tree = ast.parse(test_code)
            transformer = _PassReplacer(function_to_test_name)
            new_tree = transformer.visit(tree)
            ast.fix_missing_locations(new_tree)
            return ast.unparse(new_tree)
        except (SyntaxError, TypeError) as e:
            self._logger.warning(
                "AST transformation for validation logic failed: %s. "
                "Falling back to string replacement.", e
            )
            # Fallback to less robust string replacement if AST fails
            return test_code.replace("    pass", f"    assert {function_to_test_name}(**test_input) == expected_output")
            return test_code.replace("    pass", validation_logic, 1)