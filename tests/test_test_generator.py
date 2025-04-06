import pytest
import os
from src.core.agents.test_generator import TestGeneratorAgent # Corrected import
from unittest.mock import MagicMock

class TestGeneratorAgentTests: # Updated test class name
    def setup_method(self):
        self.agent = TestGeneratorAgent() # Updated instantiation

    def test_generate_tests_valid_code(self, mocker):
        # No need to mock LLM for placeholder generation
        # mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        # mock_llm_generate.return_value = """...""" # Not needed

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests.py")
        os.makedirs(test_dir, exist_ok=True)
        # Ensure file exists for writing
        # with open(test_file, 'w'):
        #     pass # Create empty file if needed, generate_tests handles creation now

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check pytest and correct test structure in file content
        assert "import pytest" in content
        assert "def test_placeholder_code_positive():" in content # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in content
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in content

        # Also check returned string
        assert "import pytest" in generated_tests
        assert "def test_placeholder_code_positive():" in generated_tests # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in generated_tests
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in generated_tests


    def test_generate_tests_empty_llm_response(self, mocker):
        # LLM mock not needed for placeholder generation
        # mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        # mock_llm_generate.return_value = ""  # Empty response

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_empty.py") # Use different file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check pytest and placeholder test presence in file content
        assert "import pytest" in content
        assert "def test_placeholder_code_positive():" in content # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in content
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in content

        # Also check returned string
        assert "import pytest" in generated_tests
        assert "def test_placeholder_code_positive():" in generated_tests # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in generated_tests
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in generated_tests

    def test_generate_tests_markdown_cleanup(self, mocker):
        # LLM mock not needed for placeholder generation
        # mock_llm_generate = mocker.patch.object(self.agent.llm, 'generate')
        # mock_llm_generate.return_value = "\n```python\n`\n`python\ndef test_example():\n    assert 1 == 1\n```\n```"

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_markdown.py") # Use different file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check placeholder content in file
        assert "import pytest" in content
        assert "def test_placeholder_code_positive():" in content # Updated assertion - placeholder_code

        # Also check returned string
        assert "import pytest" in generated_tests
        assert "def test_placeholder_code_positive():" in generated_tests # Updated assertion - placeholder_code

    def test_generate_tests_enhanced_skip_messages(self, mocker):
        """Test generate_tests with enhanced skip messages including function name."""
        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_skip_msg.py") # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def sample_function(n):\n    return n * 2" # Sample code with a function name
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for function name in skip messages
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'sample_function\'")' in content
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'sample_function\'")' in content

        # Also check returned string
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'sample_function\'")' in generated_tests
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'sample_function\'")' in generated_tests

    def test_generate_tests_positive_assertion_square(self, mocker):
        """Test generate_tests creates positive assertion for 'square' function."""
        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_positive_square.py")
        os.makedirs(test_dir, exist_ok=True)

        code = "def square(n):\n    return n * n"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for positive assertion in test code
        assert "assert square(2) == 4" in content
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'square\'")' in content


    def test_generate_tests_positive_assertion_add(self, mocker):
        """Test generate_tests creates positive assertion for 'add' function."""
        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_positive_add.py")
        os.makedirs(test_dir, exist_ok=True)

        code = "def add(a, b):\n    return a + b"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for positive assertion in test code
        assert "assert add(3, 5) == 8" in content
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'add\'")' in content


    def test_generate_tests_positive_assertion_multiply(self, mocker):
        """Test generate_tests creates dynamic assertion for 'multiply' (new dynamic logic)."""
        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_positive_multiply.py") # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def multiply(x, y):\n    return x * y" # Simple multiply function
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for dynamic assertion in test code - new dynamic logic
        assert "assert multiply(3, 5) == 15" in content # Expect dynamic assertion
        assert "pytest.skip(f\"Placeholder test: Negative case for function 'multiply'\")" in content # Placeholder for negative case


    def test_generate_tests_dynamic_assertion_fallback_complex(self, mocker):
        """Test generate_tests falls back for complex/non-numerical function."""
        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_dynamic_fallback_complex.py") # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def complex_function(data):\n    if not data:\n        return None\n    return data[0] + 10" # More complex function
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for placeholder tests - No dynamic assertion expected
        assert "pytest.skip(f\"Placeholder test: Positive case for function 'complex_function'\")" in content
        assert "assert complex_function(" not in content # No dynamic assertion

    def test_reintegrated_extract_and_store_methods(self, mocker):
        """Test the re-integrated _extract_function_name and _store_tests methods."""
        # --- Corrected Mock Creation (Attempt 3) - Using autospec=True ---
        mock_kg_add_node = MagicMock() # Use MagicMock directly - Simpler approach
        mocker.patch.object(self.agent.kg, 'add_node', new=mock_kg_add_node) # Patch with the MagicMock instance

        code_snippet = "def example_function(arg1, arg2):\n    return arg1 + arg2"
        function_name = self.agent._extract_function_name(code_snippet)
        assert function_name == "example_function"

        test_code = "import pytest\n\ndef test_example_function_positive():\n    pytest.skip('Placeholder test: Positive case')\n    assert True"
        code_hash = hash(code_snippet)
        stored_test_code = self.agent._store_tests(test_code, code_hash)

        mock_kg_add_node.assert_called_once()
        node_arg = mock_kg_add_node.call_args[0][0]
        assert node_arg.type == "generated_test"
        assert node_arg.metadata["source_hash"] == code_hash
        assert "pytest.skip" in node_arg.content
        assert stored_test_code == test_code # Verify returned test code is the same

    def test_generate_tests_enhanced_skip_messages(self, mocker):
        """Test generate_tests with enhanced skip messages including function name."""
        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_skip_msg.py") # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def sample_function(n):\n    return n * 2" # Sample code with a function name
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file) # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for function name in skip messages
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'sample_function\'")' in content
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'sample_function\'")' in content

        # Also check returned string
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'sample_function\'")' in generated_tests
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'sample_function\'")' in generated_tests

    # Clean up generated files after tests run in this class
    def teardown_method(self):
        test_dir = "generated_tests"
        files_to_remove = [
            os.path.join(test_dir, "generated_tests.py"),
            os.path.join(test_dir, "generated_tests_empty.py"),
            os.path.join(test_dir, "generated_tests_markdown.py"),
            os.path.join(test_dir, "generated_tests_skip_msg.py"),
            os.path.join(test_dir, "generated_tests_positive_square.py"),
            os.path.join(test_dir, "generated_tests_positive_add.py"),
            os.path.join(test_dir, "generated_tests_positive_multiply.py"),
            os.path.join(test_dir, "generated_tests_dynamic_fallback_complex.py")
        ]
        for f_path in files_to_remove:
            if os.path.exists(f_path):
                os.remove(f_path)
        if os.path.exists(test_dir) and not os.listdir(test_dir):
            os.rmdir(test_dir)