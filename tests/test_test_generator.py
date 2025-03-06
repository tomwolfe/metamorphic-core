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

        code = "placeholder_code"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis)

        # Check returned value (includes placeholder)
        assert "def placeholder_code(n):" in generated_tests
        assert "def test_positive_number():" in generated_tests
        assert "def test_negative_number():" in generated_tests

        # Check file content
        with open("generated_tests/generated_tests.py", "r") as f:
            file_content = f.read()
        assert "def placeholder_code(n):" in file_content
        assert "def test_positive_number():" in file_content
        assert "def test_negative_number():" in file_content

    def test_generate_tests_empty_llm_response(self, mocker):
        mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        mock_llm_generate.return_value = ""  # Empty response

        code = "placeholder_code"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis)

        # Check returned value (placeholder exists)
        assert "def placeholder_code(n):" in generated_tests
        assert "def test_positive_number():" not in generated_tests
        assert "def test_negative_number():" not in generated_tests

        # Verify file content
        with open("generated_tests/generated_tests.py", "r") as f:
            file_content = f.read()
        assert "def placeholder_code(n):" in file_content
        assert "def test_positive_number():" not in file_content
        assert "def test_negative_number():" not in file_content

    def test_generate_tests_markdown_cleanup(self, mocker):
        mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        mock_llm_generate.return_value = "\n```python\n`\n`python\ndef test_example():\n    assert 1 == 1\n```\n```"

        generated_tests = self.agent.generate_tests("test_code", {})

        assert "def placeholder_code(n):" in generated_tests  # Placeholder is always present
        assert "def test_example():" in generated_tests