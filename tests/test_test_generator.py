import pytest
import os
from src.core.agents.test_generator import TestGenAgent

class TestTestGenAgent:
    def setup_method(self):
        self.agent = TestGenAgent()

    def test_generate_tests_valid_code(self, mocker):
        mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        mock_llm_generate.return_value = """```python
def test_positive_number():
    assert placeholder_code(5) == 5

def test_negative_number():
    assert placeholder_code(-5) == -5
    ```"""

        test_dir = "generated_tests"
        os.makedirs(test_dir, exist_ok=True)
        with open(f"{test_dir}/generated_tests.py", 'w'):
            pass  # Create empty file

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis)

        # Check pytest and correct test structure
        assert "import pytest" in generated_tests
        assert "def test_placeholder_function_positive():" in generated_tests  # Updated assertion
        assert "def test_placeholder_function_negative():" in generated_tests  # Added assertion
        assert 'pytest.skip("Placeholder test: Positive case")' in generated_tests
        assert 'pytest.skip("Placeholder test: Negative case")' in generated_tests

    def test_generate_tests_empty_llm_response(self, mocker):
        mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        mock_llm_generate.return_value = ""  # Empty response

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis)

        # Check pytest and placeholder test presence
        assert "import pytest" in generated_tests
        assert "def test_placeholder_function_positive():" in generated_tests # Updated assertion
        assert "def test_placeholder_function_negative():" in generated_tests # Added assertion
        assert 'pytest.skip("Placeholder test' in generated_tests

    def test_generate_tests_markdown_cleanup(self, mocker):
        mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        mock_llm_generate.return_value = "\n```python\n`\n`python\ndef test_example():\n    assert 1 == 1\n```\n```"

        code = "def placeholder_code(n):\n    pass" 
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis)

        assert "import pytest" in generated_tests
        assert "def test_placeholder_function_positive():" in generated_tests # Updated assertion
        assert 'pytest.skip("Placeholder test' in generated_tests