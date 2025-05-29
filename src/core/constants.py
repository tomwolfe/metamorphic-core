# src/core/constants.py

# File Handling Constants
MAX_READ_FILE_SIZE = 1024 * 1024  # 1 MB
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"
END_OF_CODE_MARKER = "# METAMORPHIC_END_OF_CODE_SNIPPET"

# Workflow Driver Constants
MAX_STEP_RETRIES = 2  # Allows 2 retries per step (3 attempts total)

# New constant for minimal context instruction (Task 1.8.A)
CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION = (
    "You have been provided with a **targeted, minimal section** of the source file relevant to the current step. "
    "Your task is to implement the required changes within this context. "
    "Do NOT output the entire file content. Only provide the new or changed lines."
)

# Coder LLM Prompt Guidelines
GENERAL_SNIPPET_GUIDELINES = (
    "1. Ensure all string literals are correctly terminated (e.g., matching quotes, proper escaping).\n"
    "2. Pay close attention to Python's indentation rules. Ensure consistent and correct internal indentation. If inserting into existing code, the snippet's base indentation should align with the insertion point if a METAMORPHIC_INSERT_POINT is present. Use 4 spaces per indentation level.\n" # Enhanced indentation
    "3. Generate complete and runnable Python code snippets. Avoid partial statements, unclosed parentheses/brackets/braces, or missing colons.\n"
    "4. If modifying existing code, ensure the snippet integrates seamlessly and maintains overall syntactic validity.\n"
    "5. **CRITICAL PEP 8 ADHERENCE:** All generated Python code snippets MUST strictly adhere to PEP 8 style guidelines. This is mandatory for code acceptance.\n"
    "   - **Line Length:** Strictly keep lines under 80 characters (preferably 79). Use Python's line continuation methods (e.g., within parentheses, brackets, braces, or using a backslash `\\`) for long statements.\n"
    "   - **Comment Spacing:** Inline comments MUST start with `#` and a single space, and be preceded by at least two spaces (e.g., `x = 1  # This is a comment`). Block comments should also follow this pattern for each line.\n"
    "   - **Indentation:** Use 4 spaces per indentation level. Ensure consistent and correct indentation within your snippet.\n"
    "   - **Imports (IMPORTANT - READ CAREFULLY FOR SNIPPETS):\n"
    "     - If the task is to add or modify import statements at the top of a file, output *only* the `import` or `from ... import ...` lines.\n"
    "     - If generating a new method or function snippet for an existing Python file:\n"
    "       - For standard library modules (e.g., `os`, `sys`, `re`, `json`, `datetime`, `pathlib.Path`, `typing.Optional`, `typing.List`, `ast`) that are commonly imported at the file level, **assume these are already imported in the target file.** Do NOT include these `import` statements within your generated method/function snippet. Your snippet should be *only* the method/function definition.\n"
    "       - **EXCEPTION FOR VALIDATION:** If your new method/function snippet uses types/modules like `Path`, `Optional`, `List`, `Dict`, `Any`, `Tuple`, `Union` from `pathlib` or `typing`, or modules like `ast`, `re`, `json`, `datetime`, YOU MUST INCLUDE the necessary `from X import Y` statements (e.g., `from pathlib import Path`, `from typing import Optional, List`, `import ast`) AT THE TOP OF YOUR SNIPPET. This is required for your snippet to pass isolated pre-write validation checks. These snippet-local imports might be removed later if they are redundant with existing imports in the full file.\n"
    "       - If your snippet *requires* a new third-party library, you MAY include the import at the start of your snippet.\n"
    "     - For any other type of snippet (e.g., a standalone script, or if unsure), ensure all necessary imports are at the beginning of your snippet.\n"
    "6. Logging: If logging is required within a class method, use `self.logger.debug(...)`, `self.logger.info(...)`, etc., assuming `self.logger` is available. For standalone functions or scripts, ensure `logger` is properly initialized (e.g., `import logging; logger = logging.getLogger(__name__)`) if not provided in context.\n"
    "7. F-strings: Ensure all f-strings are correctly formatted with placeholders if variables are intended (e.g., `f'Value is {{my_variable}}'`). If an f-string is meant to be literal (e.g., in a regex pattern that uses curlies), ensure it does not contain unmatched curly braces that would cause a `SyntaxError` during f-string parsing, or use a raw string `r''` if appropriate."
)

# CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS is a template string that needs to be formatted
# with END_OF_CODE_MARKER when used.
CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS = (
    "CRITICAL INSTRUCTIONS FOR YOUR RESPONSE FORMAT:\n"
    "1. Your entire response MUST be ONLY a valid Python code snippet.\n"
    "2. Do NOT include any explanations, introductory text, apologies, or markdown formatting like ```python or ```.\n"
    "3. The Python code snippet you generate will be directly parsed and inserted into an existing Python file.\n"
    "4. Your Python code snippet MUST end with the exact marker line, on its own line, with no preceding or trailing characters on that line: `{{END_OF_CODE_MARKER}}` (e.g., `# {{METAMORPHIC_END_OF_CODE_SNIPPET}}`)\n"  # New point 4
    "5. ALWAYS output *only* the minimal changed/new lines. Do NOT repeat unchanged lines from the existing file. Examples:\n"  # Old point 4, now point 5
    "   - To add an import: `import new_module`\n"
    "   - To add a new method to a class: `    def new_method(self):\n        \"\"\"New method docstring.\"\"\"\n        pass`\n"
    "   - To change a single line: `    return new_value`\n"
    "6. If the plan step asks for an explanation or analysis, output only a Python comment explaining the error and the `{{METAMORPHIC_END_OF_CODE_SNIPPET}}` marker."  # Old point 5, now point 6
)

# Instruction for CoderLLM on output format for targeted modifications
CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS = (
    "\n\nIMPORTANT: For targeted modifications (e.g., adding an import, inserting a method):\n"
    "- Output *only* the new/changed code block.\n"
    "- Examples:\n"
    "  - New import: `import new_module`\n"
    "  - New method: `def new_method(self):\n    pass`\n"
    "- Avoid entire files or large unchanged sections."
)

# Python Code Creation Keywords (for docstring instruction)
DOCSTRING_INSTRUCTION_PYTHON = (
    "IMPORTANT: For any new Python functions, methods, or classes, you MUST include a comprehensive PEP 257 compliant docstring. Use Google-style format (Args:, Returns:, Example: sections). This is required to pass automated ethical and style checks."
) # Removed trailing space
PYTHON_CREATION_KEYWORDS = [ # Task 1.8.Y: Keywords indicating creation of new Python code structures
    "implement function", "add method", "create class", "define function",
    "write function", "write method", "write class",
    "implement a function", "add a method", "create a class", "define a function",
    "write a function", "write a method", "a class",
    "new function", "new method", "new class", "generate function",
    "generate method", "generate class", "add function to", "add method to", "add class to",
    "write a new function", "write a python function", "write a new python function",
    "create a new function", "create a python function", "create a new python function",
    "define a new function", "define a python function",
    "define a new class", "define a python class",
    "define a new global function", # Added for test coverage
    "define new global function", # Additional pattern for variation (already present)
    "define a global function",
    "define a python function",
    "define a new python function",
    "define a new python class", # Added keyword for test case
    "implement a new function", "implement a python function", "implement a new python function",
    "add a new method", "add a python method", "add a new python method",
    "create a new class", "create a python class", "create a new python class",
    "define a new class", "define a python class",
    "implement a new class", "implement a python class", "implement a new python class",
    # These were already in constants, but ensure they are covered
    "add function", "add method", "add class", "test case", # Added for docstring robustness
    # Added for Phase 1.8 docstring robustness (Task: unblock task_1_8_A_optimize_large_context)
    "develop test case", "write test method", "create test class", # For test generation
    "add logic", "implement logic", "define logic", # For adding significant blocks
    "refactor function", "refactor method", # For substantial rewrites that might need new/updated docstrings
    "add helper function", "implement helper function", "define helper method", # For new helpers
    "enhance prompt construction", "modify prompt construction", # For tasks involving prompt logic changes
]


# General reminder for docstrings in Python files
GENERAL_PYTHON_DOCSTRING_REMINDER = (
    "REMINDER: If new Python functions, methods, or classes are created, or if existing ones "
    "are significantly modified to implement this step, ensure they include (or have updated) "
    "comprehensive PEP 257 compliant docstrings. Use Google-style format (Args:, Returns:, Example: sections). "
    "This is important for code maintainability and to pass automated checks."
)

# New critical output instructions specifically for full Python blocks (functions, methods, classes)
CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS = (
    "CRITICAL INSTRUCTIONS FOR YOUR RESPONSE FORMAT (Full Block/Method/Class Focus):\n"
    "1. Your entire response MUST be ONLY a valid Python code snippet representing the complete new or modified function, method, or class.\n"
    "2. Do NOT include any explanations, introductory text, apologies, or markdown formatting like ```python or ```.\n"
    "3. The Python code snippet you generate will be directly parsed and then merged.\n"
    "4. Your Python code snippet MUST end with the exact marker line, on its own line: `{END_OF_CODE_MARKER}`\n"
    "5. Ensure the generated function/method/class is syntactically correct and complete in itself.\n"
    "6. The base indentation of your snippet should be 0 (i.e., the `def` or `class` keyword should not be indented within the snippet itself), unless the snippet is meant to be a nested structure that is itself a complete parsable unit.\n"
)