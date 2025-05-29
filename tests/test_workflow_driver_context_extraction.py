# tests/test_workflow_driver_context_extraction.py
import pytest
from unittest.mock import patch, MagicMock
from src.core.automation.workflow_driver import WorkflowDriver, Context, MAX_IMPORT_CONTEXT_LINES, CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION, CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS, CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS, END_OF_CODE_MARKER, PYTHON_CREATION_KEYWORDS
from pathlib import Path
import ast
import logging # Added for caplog
import re # Added for regex in tests

@pytest.fixture
def driver_for_context_tests(tmp_path, mocker):
    context = Context(str(tmp_path))
    mocker.patch.object(WorkflowDriver, '_load_default_policy') # Mock policy loading
    driver = WorkflowDriver(context)
    driver.llm_orchestrator = MagicMock()
    driver.default_policy_config = {'policy_name': 'Mock Policy'}
    # Mock PYTHON_CREATION_KEYWORDS on the instance if it's accessed via self
    # If it's a global, this isn't strictly needed but doesn't hurt.
    driver.PYTHON_CREATION_KEYWORDS = PYTHON_CREATION_KEYWORDS 
    return driver

class TestWorkflowDriverContextExtraction:

    # --- Tests for _get_context_type_for_step ---
    @pytest.mark.parametrize("step_description, expected_type", [
        ("Add import os", "add_import"),
        ("Implement new import for pathlib", "add_import"),
        ("Add method process_data to class DataProcessor", "add_method_to_class"),
        ("Add method process_data to class DataProcessor_new", "add_method_to_class"), # Test with underscore
        ("Define function calculate_results in the main module", "add_global_function"),
        ("Refactor the existing calculate_results function", None), # "Refactor" implies modification, not new creation, so full context
        ("Create a new class UserProfile", None), # New class defaults to None (full context)
        ("Update the README.md file", None),
        ("Implement a new function called `my_func`", "add_global_function"), # Now correctly matches
        ("Define a new method for processing items", "add_global_function"), # Generic method, not to specific class
        ("Add a new class MyNewClass", None), # Explicit new class
        ("Create class MyOtherClass", None),  # Explicit new class
        ("Generate class MyGeneratedClass", None), # Explicit new class
        ("Add some imports", "add_import"), # Now correctly matches
        ("Add a new method to an existing class called MyDataHandler", "add_method_to_class"), # Now correctly matches
        ("Define a new global function for utility purposes", "add_global_function"), # Now correctly matches
        ("Just analyze the code", None), # Ambiguous, defaults to None
    ])
    def test_get_context_type_for_step(self, driver_for_context_tests, step_description, expected_type):
        assert driver_for_context_tests._get_context_type_for_step(step_description) == expected_type

    # --- Tests for _extract_targeted_context ---
    def test_extract_targeted_context_add_import_existing_imports(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        file_content = "# Initial comment\nimport os\nimport sys\n\n# Comment between imports\nfrom pathlib import Path\n\n# Another comment\ndef func():\n    pass\n# Trailing comment"
        file_path = str(tmp_path / "test_module.py") # Create a dummy file path
        
        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, "add_import", "Add import json")
        
        assert is_minimal is True
        assert "import os" in context_str
        assert "import sys" in context_str
        assert "from pathlib import Path" in context_str
        assert "# Initial comment" in context_str # Buffer line before (line 1)
        assert "# Another comment" in context_str # Buffer line after (line 7)
        assert "def func():" not in context_str # Should not include code outside import block
        
        # Expected lines based on new buffer (min_line-2 to max_line+2)
        # min_line=2, max_line=5 (1-indexed) -> start_idx=0, end_idx=7 (0-indexed)
        expected_context = "\n".join(file_content.splitlines()[0:8]) # Adjusted to match new buffer (max_line + 3)
        assert context_str.strip() == expected_context.strip()

    def test_extract_targeted_context_add_import_no_existing_imports(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        # Simplified content to ensure AST parsing doesn't fail on large dummy data
        file_content = "# Initial comment\n" + "\n".join([f"# line {i}" for i in range(MAX_IMPORT_CONTEXT_LINES - 1)]) # Ensure it's exactly MAX_IMPORT_CONTEXT_LINES lines and valid Python
        file_path = str(tmp_path / "test_module.py") # Create a dummy file path

        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, "add_import", "Add import json")
        
        assert is_minimal is True
        assert len(context_str.splitlines()) == MAX_IMPORT_CONTEXT_LINES # Should contain exactly MAX_IMPORT_CONTEXT_LINES lines
        assert context_str.startswith("# Initial comment")

    def test_extract_targeted_context_add_method_to_class(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        file_content = """
# Line 1: Preamble
import os # Line 2

# Line 4: Blank line
class MyProcessor: # Line 5
    def __init__(self): # Line 6
        self.data = None # Line 7

    def load_data(self, path): # Line 9
        self.data = path # Line 10
        # METAMORPHIC_INSERT_POINT for new method # Line 11
        # end_lineno for load_data is 11
# end_lineno for MyProcessor is 11

# Epilogue
def helper_func():
    pass
"""
        file_path = str(tmp_path / "processor.py")
        step_desc = "Add method process_item to class MyProcessor"
    
        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, "add_method_to_class", step_desc)
            
        assert is_minimal is True
        assert "class MyProcessor:" in context_str
        assert "def __init__(self):" in context_str
        assert "def load_data(self, path):" in context_str
        assert "# METAMORPHIC_INSERT_POINT for new method" in context_str
        assert "# Line 1: Preamble" in context_str # Should be included due to buffer and class context logic
        assert "import os" in context_str # Should be included due to buffer (line 3)
        assert "def helper_func():" not in context_str
        assert context_str.strip().startswith("# Line 1: Preamble") # The stripped context should start with the first non-blank line, which is the preamble comment.
        assert context_str.strip().endswith("# METAMORPHIC_INSERT_POINT for new method # Line 11")

    def test_extract_targeted_context_unknown_type_or_non_python(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        file_content = "Some text content."
        text_file_path = str(tmp_path / "notes.txt")
        python_file_path = str(tmp_path / "script.py")

        context_str, is_minimal = driver._extract_targeted_context(python_file_path, file_content, "unknown_type", "Do something")
        assert is_minimal is False
        assert context_str == file_content

        context_str, is_minimal = driver._extract_targeted_context(text_file_path, file_content, "add_import", "Add import to text file")
        assert is_minimal is False
        assert context_str == file_content
        
    def test_extract_targeted_context_syntax_error_in_file(self, driver_for_context_tests, tmp_path, caplog):
        driver = driver_for_context_tests
        file_content = "def func_a():\n  print('valid')\n\ndef func_b()\n  print('invalid syntax')" 
        file_path = str(tmp_path / "broken_syntax.py")

        with caplog.at_level(logging.WARNING):
            context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, "add_method_to_class", "Add method to class NonExistent")
        
        assert is_minimal is False
        assert context_str == file_content
        assert f"SyntaxError parsing {file_path} for targeted context extraction. Falling back to full content." in caplog.text

    def test_method_addition_gets_class_and_surrounding_context(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        file_content = "import pandas\nimport numpy as np\n\nclass DataProcessor:\n    def existing_method(self):\n        pass\n\n# Other code"
        file_path = str(tmp_path / "data_proc.py")
        # Step description must match the regex in _get_context_type_for_step and _extract_targeted_context
        step_desc = "Add method process_data to class DataProcessor"
    
        context_type = driver._get_context_type_for_step(step_desc) # Get type first
        assert context_type == "add_method_to_class"
    
        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, context_type, step_desc)
    
        assert is_minimal is True
        assert "class DataProcessor:" in context_str
        assert "def existing_method(self):" in context_str
        # With increased buffer, imports are now expected to be included if they are close enough
        assert "import pandas" in context_str
        assert "import numpy as np" in context_str

    # --- Tests for _construct_coder_llm_prompt with minimal context ---
    def test_construct_coder_llm_prompt_with_minimal_context(self, driver_for_context_tests):
        driver = driver_for_context_tests
        task = {'task_name': 'Test Task', 'description': 'Test Description'}
        step = "Add import os"
        filepath = "test.py"
        minimal_context_str = "import sys"
        # Mock _should_add_docstring_instruction to return False for this test
        with patch.object(driver, '_should_add_docstring_instruction', return_value=False):
            prompt = driver._construct_coder_llm_prompt(task, step, filepath, minimal_context_str, is_minimal_context=True)

        assert CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION in prompt
        assert "PROVIDED CONTEXT FROM `test.py` (this might be the full file or a targeted section):\n\nimport sys" in prompt
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in prompt
        assert CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS in prompt

    def test_construct_coder_llm_prompt_with_full_context(self, driver_for_context_tests):
        driver = driver_for_context_tests
        task = {'task_name': 'Test Task', 'description': 'Test Description'}
        step = "Implement new feature"
        filepath = "test.py"
        full_context_str = "import sys\n\ndef main():\n    pass"
        # Mock _should_add_docstring_instruction to return False for this test
        with patch.object(driver, '_should_add_docstring_instruction', return_value=False):
            prompt = driver._construct_coder_llm_prompt(task, step, filepath, full_context_str, is_minimal_context=False)

        assert CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION not in prompt
        assert "PROVIDED CONTEXT FROM `test.py` (this might be the full file or a targeted section):\n\nimport sys" in prompt
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) in prompt
        assert CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS in prompt

    # --- Test for _should_add_docstring_instruction simplification ---
    def test_should_add_docstring_instruction_simplified_check(self, driver_for_context_tests):
        driver = driver_for_context_tests
        # This test implicitly relies on PYTHON_CREATION_KEYWORDS being available.
        # The fixture sets it on the driver instance.
        assert driver._should_add_docstring_instruction("Implement new function foo", "test.py") is True
        # Verify no error is logged about PYTHON_CREATION_KEYWORDS not being defined
        # (This would require checking caplog if the logger was configured to error level for this)


class TestPhase1_8Features:
    def test_research_step_classification(self, driver_for_context_tests):
        driver = driver_for_context_tests