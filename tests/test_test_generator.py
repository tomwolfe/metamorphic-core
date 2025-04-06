import pytest
import os
from src.core.agents.test_generator import TestGeneratorAgent  # Corrected import
from unittest.mock import MagicMock

# Apply the patch at the module level, mocking KnowledgeGraph class itself
@pytest.fixture(autouse=True)
def mock_knowledge_graph_class(mocker):
    """Fixture to mock the KnowledgeGraph class for all tests in this module."""
    return mocker.patch("src.core.agents.test_generator.KnowledgeGraph", autospec=True)  # Mock KnowledgeGraph class


class TestGeneratorAgentTests:  # Updated test class name
    def setup_method(self):
        self.agent = TestGeneratorAgent()  # Updated instantiation - will use mocked KG

    def test_generate_tests_valid_code(self, mocker, mock_knowledge_graph_class):  # Inject the fixture
        # mock_knowledge_graph_class is now injected, ensuring KG is mocked

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests.py")
        os.makedirs(test_dir, exist_ok=True)
        # Ensure file exists for writing
        # with open(test_file, 'w'):
        #     pass # Create empty file if needed, generate_tests handles creation now

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check pytest and correct test structure in file content
        assert "import pytest" in content
        assert "def test_placeholder_code_positive():" in content  # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in content
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in content

        # Also check returned string
        assert "import pytest" in generated_tests
        assert "def test_placeholder_code_positive():" in generated_tests  # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in generated_tests
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in generated_tests

    def test_generate_tests_empty_llm_response(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_empty.py")  # Use different file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check pytest and placeholder test presence in file content
        assert "import pytest" in content
        assert "def test_placeholder_code_positive():" in content  # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in content
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in content

        # Also check returned string
        assert "import pytest" in generated_tests
        assert "def test_placeholder_code_positive():" in generated_tests  # Updated assertion - placeholder_code
        assert "def test_placeholder_code_negative():" in generated_tests
        assert 'pytest.skip(f"Placeholder test: Positive case for function \'placeholder_code\'")' in generated_tests

    def test_generate_tests_markdown_cleanup(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_markdown.py")  # Use different file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def placeholder_code(n):\n    pass"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check placeholder content in file
        assert "import pytest" in content
        assert "def test_placeholder_code_positive():" in content  # Updated assertion - placeholder_code

        # Also check returned string
        assert "import pytest" in generated_tests
        assert "def test_placeholder_code_positive():" in generated_tests  # Updated assertion - placeholder_code

    def test_generate_tests_enhanced_skip_messages(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_skip_msg.py")  # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def sample_function(n):\n    return n * 2"  # Sample code with a function name
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

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

    def test_generate_tests_positive_assertion_square(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_positive_square.py")
        os.makedirs(test_dir, exist_ok=True)

        code = "def square(n):\n    return n * n"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for positive assertion in test code
        assert "assert square(2) == 4" in content
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'square\'")' in content

    def test_generate_tests_positive_assertion_add(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_positive_add.py")
        os.makedirs(test_dir, exist_ok=True)

        code = "def add(a, b):\n    return a + b"
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for positive assertion in test code
        assert "assert add(3, 5) == 8" in content
        assert 'pytest.skip(f"Placeholder test: Negative case for function \'add\'")' in content

    def test_generate_tests_positive_assertion_multiply(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_positive_multiply.py")  # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def multiply(x, y):\n    return x * y"  # Simple multiply function
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for dynamic assertion in test code - new dynamic logic
        assert "assert multiply(3, 5) == 15" in content  # Expect dynamic assertion
        assert "pytest.skip(f\"Placeholder test: Negative case for function 'multiply'\")" in content  # Placeholder for negative case

    def test_generate_tests_dynamic_assertion_fallback_complex(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_dynamic_fallback_complex.py")  # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def complex_function(data):\n    if not data:\n        return None\n    return data[0] + 10"  # More complex function
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

        # Check file content
        assert os.path.exists(test_file)
        with open(test_file, 'r') as f:
            content = f.read()

        # Check for placeholder tests - No dynamic assertion expected
        assert "pytest.skip(f\"Placeholder test: Positive case for function 'complex_function'\")" in content
        assert "assert complex_function(" not in content  # No dynamic assertion

    def test_reintegrated_extract_and_store_methods(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected

        # --- Corrected Mock Creation (Attempt 3) - Using autospec=True ---
        mocked_kg_add_node = mock_knowledge_graph_class.return_value.add_node  # Access mock through fixture

        code_snippet = "def example_function(arg1, arg2):\n    return arg1 + arg2"
        function_name = self.agent._extract_function_name(code_snippet)
        assert function_name == "example_function"

        test_code = "import pytest\n\ndef test_example_function_positive():\n    pytest.skip('Placeholder test: Positive case')\n    assert True"
        code_hash = hash(code_snippet)
        stored_test_code = self.agent._store_tests(test_code, code_hash)

        mocked_kg_add_node.assert_called_once()  # Assert that mock was called
        node_arg = mocked_kg_add_node.call_args[0][0]  # Get the return_value of the mock
        assert node_arg.type == "generated_test"
        assert node_arg.metadata["source_hash"] == code_hash
        assert "pytest.skip" in node_arg.content
        assert stored_test_code == test_code  # Verify returned test code is the same

    def test_generate_tests_enhanced_skip_messages(self, mocker, mock_knowledge_graph_class):  # Inject fixture
        # mock_knowledge_graph_class is injected
        test_dir = "generated_tests"
        test_file = os.path.join(test_dir, "generated_tests_skip_msg.py")  # New file name
        os.makedirs(test_dir, exist_ok=True)

        code = "def sample_function(n):\n    return n * 2"  # Sample code with a function name
        spec_analysis = {}
        generated_tests = self.agent.generate_tests(code, spec_analysis, file_path=test_file)  # Pass file_path

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
        # self.agent.kg.add_node = self.original_add_node  # No need to restore mock anymore
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