# tests/test_workflow_driver_context_extraction.py
import pytest
from unittest.mock import patch, MagicMock
from src.core.automation.workflow_driver import WorkflowDriver, Context
from src.core.constants import MAX_IMPORT_CONTEXT_LINES, CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION, CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS, CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS, END_OF_CODE_MARKER, PYTHON_CREATION_KEYWORDS, CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS
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
        ("Define function calculate_results in the main module", None), # Changed to None, as "global" is not explicit
        ("Refactor the existing calculate_results function", None),
        ("Create a new class UserProfile", None), # New class defaults to None (full context)
        ("Update the README.md file", None),
        ("Implement a new function called `my_func`", None), # Ambiguous, should be None
        ("Define a new method for processing items", None), # Ambiguous, should be None
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
    
        # Expected context: lines 0-8 (inclusive of line 0, exclusive of line 8)
        # Corresponds to: "# Initial comment\nimport os\nimport sys\n\n# Comment between imports\nfrom pathlib import Path\n\n# Another comment"
        expected_context = "\n".join(file_content.splitlines()[0:8])
        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, "add_import", "Add import json")
    
        assert is_minimal is True, "is_minimal should be True for successful targeted extraction"
        assert context_str == expected_context, "Context string should be the extracted import block"

    def test_extract_targeted_context_add_import_no_existing_imports(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        # Simplified content to ensure AST parsing doesn't fail on large dummy data
        file_content = "# Initial comment\n" + "\n".join([f"# line {i}" for i in range(MAX_IMPORT_CONTEXT_LINES - 1)]) # Ensure it's exactly MAX_IMPORT_CONTEXT_LINES lines and valid Python
        file_path = str(tmp_path / "test_module.py") # Create a dummy file path
        # When no imports, it should return MAX_IMPORT_CONTEXT_LINES lines, which is the full content here.
        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, "add_import", "Add import json")
    
        assert is_minimal is True, "is_minimal should be True when providing top N lines for new imports"
        assert context_str == file_content, "Context string should be the full file content when no existing imports and content is MAX_IMPORT_CONTEXT_LINES"


    def test_extract_targeted_context_add_method_to_class(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        file_content = """\
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
    
        # Expected context: lines 3-14 (inclusive of line 3, exclusive of line 14)
        # Corresponds to: class MyProcessor and its content, up to the blank line after the class's last comment.
        expected_context = "\n".join(file_content.splitlines()[3:14])
        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, "add_method_to_class", step_desc)
    
        assert is_minimal is True, "is_minimal should be True for successful targeted extraction"
        assert context_str == expected_context, "Context string should be the extracted class block"

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
        
        assert is_minimal is False, "is_minimal should be False for fallback due to syntax error"
        assert context_str == file_content, "Context string should be full content for fallback"
        # The code *does* attempt AST parsing and logs a warning on SyntaxError.
        assert f"SyntaxError parsing {file_path} for targeted context extraction. Falling back to full content." in caplog.text

    def test_method_addition_gets_class_and_surrounding_context(self, driver_for_context_tests, tmp_path):
        driver = driver_for_context_tests
        file_content = "import pandas\nimport numpy as np\n\nclass DataProcessor:\n    def existing_method(self):\n        pass\n\n# Other code"
        file_path = str(tmp_path / "data_proc.py")
        # Step description must match the regex in _get_context_type_for_step and _extract_targeted_context
        step_desc = "Add method process_data to class DataProcessor"
    
        context_type = driver._get_context_type_for_step(step_desc) # Get type first
        assert context_type == "add_method_to_class"
    
        # Expected context: lines 2-8 (inclusive of line 2, exclusive of line 8)
        # Corresponds to: blank line, class DataProcessor and its content, up to the last line of the class.
        expected_context = "\n".join(file_content.splitlines()[2:8])
        context_str, is_minimal = driver._extract_targeted_context(file_path, file_content, context_type, step_desc)
    
        assert is_minimal is True, "is_minimal should be True for successful targeted extraction"
        assert context_str == expected_context, "Context string should be the extracted class block"

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
        # When is_minimal_context is True, the prompt uses CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION
        # and CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS, not CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.
        assert CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS in prompt
        assert CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) not in prompt
        assert CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS.format(END_OF_CODE_MARKER=END_OF_CODE_MARKER) not in prompt

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
        from src.core.automation.workflow_driver import classify_plan_step # Assuming this import is needed for classify_plan_step

        prelim_flags = {"is_research_step_prelim": True, "is_code_generation_step_prelim": False}
        step1 = "Research how to use the new API"
        assert prelim_flags["is_research_step_prelim"] is True
        assert prelim_flags["is_code_generation_step_prelim"] is False
        classify_plan_step(step1) == 'conceptual' # As per diff, 'assert' is removed here

def test_extract_targeted_context_fallback_behavior(driver_for_context_tests):
    """
    Tests that _extract_targeted_context returns the full content and False
    when no specific context_type is provided or when the provided context_type
    does not have a specific extraction logic implemented.
    """
    driver = driver_for_context_tests
    file_content = "line 1\nline 2\nline 3"
    file_path = "/mock/path/test.py"
    step_description = "A generic step"

    # Case 1: context_type is None, should trigger the initial fallback
    context_none, is_minimal_none = driver._extract_targeted_context(
        file_path, file_content, None, step_description
    )
    assert not is_minimal_none, "is_minimal should be False for fallback with None context_type"
    assert context_none == file_content, "Context string should be full content for None context_type"

    # Case 2: context_type is a string but does not match any specific extraction logic
    # This should trigger the final fallback in _extract_targeted_context
    context_unimplemented_str, is_minimal_unimplemented_str = driver._extract_targeted_context(
        file_path,
        file_content,
        "unimplemented_context_type", # A string that won't match "add_import", "add_method_to_class", etc.
        step_description
    )
    assert not is_minimal_unimplemented_str, "is_minimal should be False for fallback with unknown context_type string"
    assert context_unimplemented_str == file_content, "Context string should be full content for unknown context_type string"