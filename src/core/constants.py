# src/core/constants.py

# File Handling Constants
MAX_READ_FILE_SIZE = 1024 * 1024  # 1 MB
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"
MAX_IMPORT_CONTEXT_LINES = 10 # Number of lines to provide as context when adding imports and no existing imports are found
END_OF_CODE_MARKER = "# METAMORPHIC_END_OF_CODE_SNIPPET"
CONTEXT_LEAKAGE_INDICATORS: list[str] = [
    '```python',
    '```',
    'As an AI language model',
    'I am a large language model',
    'I am an AI assistant',
]

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
    "2. Pay close attention to Python's indentation rules. Ensure consistent and correct internal indentation. If inserting into existing code, the snippet's base indentation should align with the insertion point if a METAMORPHIC_INSERT_POINT is present. Use 4 spaces per indentation level.\n"
    "3. Generate complete and runnable Python code snippets. Avoid partial statements, unclosed parentheses/brackets/braces, or missing colons.\n"
    "4. If modifying existing code, ensure the snippet integrates seamlessly and maintains overall syntactic validity.\n"
    "5. **CRITICAL PEP 8 ADHERENCE:** All generated Python code snippets MUST strictly adhere to PEP 8 style guidelines. This is mandatory for code acceptance.\n"
    "   - **Line Length:** Strictly keep lines under 80 characters (preferably 79). Use Python's line continuation methods (e.g., within parentheses, brackets, braces, or using a backslash `\\`) for long statements.\n"
    "   - **Comment Spacing:** Inline comments MUST start with `#` and a single space, and be preceded by at least two spaces (e.g., `x = 1  # This is a comment`). Block comments should also follow this pattern for each line.\n"
    "   - **Indentation:** Use 4 spaces per indentation level. Ensure consistent and correct indentation within your snippet.\n"
    "   - **Imports (IMPORTANT - READ CAREFULLY FOR SNIPPETS):\n"
    "     - If the task is to add or modify import statements at the top of a file, output *only* the `import` or `from ... import ...` lines.\n"
    "     - If generating a new method or function snippet for an existing Python file:\n"
    "       - For standard library modules (e.g., `os`, `sys`, `re`, `json`, `datetime`, `pathlib`, `typing`, `ast`) that are commonly imported at the file level, **assume these are already imported in the target file.** Do NOT include these `import` statements within your generated method/function snippet unless explicitly creating a self-contained, validatable snippet. Your snippet should primarily be the method/function definition.\n"
    "       - **EXCEPTION FOR VALIDATION:** If your new method/function snippet uses types/modules like `Path`, `Optional`, `List`, `Dict`, `Any`, `Tuple`, `Union` from `pathlib` or `typing`, or modules like `ast`, `re`, `json`, `datetime`, YOU MUST INCLUDE the necessary `from X import Y` statements (e.g., `from pathlib import Path`, `from typing import Optional, List`, `import ast`) AT THE TOP OF YOUR SNIPPET. This is required for your snippet to pass isolated pre-write validation checks. These snippet-local imports might be removed later if they are redundant with existing imports in the full file.\n"
    "       - If your snippet *requires* a new third-party library, you MAY include the import at the start of your snippet.\n"
    "     - For any other type of snippet (e.g., a standalone script, or if unsure), ensure all necessary imports are at the beginning of your snippet.\n"
    "6. Logging: If logging is required within a class method, use `self.logger.debug(...)`, `self.logger.info(...)`, etc., assuming `self.logger` is available. For standalone functions or scripts, ensure `logger` is properly initialized (e.g., `import logging; logger = getLogger(__name__)`) if not provided in context.\n"
    "8. **Raw Strings and Regular Expressions (CRITICAL):** When generating Python code that includes raw strings (e.g., for regular expressions), it is absolutely CRITICAL that they are correctly formatted and fully terminated. This is a common source of `SyntaxError: unterminated string literal`.\n"
    "    - **Termination:** Ensure raw strings are always closed with the correct quote type (`'` or `\"` for single-line, `'''` or `\"\"\"` for multi-line).\n"
    "    - **Escaping:** Be extremely careful with backslashes (`\\`) within raw strings. If a backslash is intended to be literal, it should be escaped (e.g., `r'C:\\\\path\\\\to\\\\file'`).\n"
    "    - **Common Error:** Avoid generating incomplete raw string literals like `r\\\"^\\\\s*` (missing closing quote) or `r'my_pattern\\'` (trailing unescaped backslash). These are common failure modes for LLMs.\n"
    "    - **Example of Correct Usage:** `pattern = r\\\"^\\\\s*\\\"` or `path = r'C:\\\\Users\\\\Name\\\\Docs'`\n"
    "    - **Example of Incorrect Usage (AVOID):** `r\\\"^\\\\s*` (missing closing quote) or `r'path\\'` (trailing unescaped backslash).\n"
    "9. Snippet Completeness: Ensure the generated snippet is a fully complete and syntactically valid block of code that can be inserted. Avoid partial lines or incomplete statements, especially at the end of the snippet. Double-check for unterminated strings or comments."
)

# CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS is a template string that needs to be formatted
# with END_OF_CODE_MARKER when used.
CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS = (
    "CRITICAL INSTRUCTIONS FOR YOUR RESPONSE FORMAT:\n"
    "1. Your entire response MUST be ONLY a valid Python code snippet.\n"
    "2. Do NOT include any explanations, introductory text, apologies, or markdown formatting like ```python or ```.\n"
    "3. The Python code snippet you generate will be directly parsed and inserted into an existing Python file.\n"
    "4. ALWAYS output *only* the minimal changed/new lines. Do NOT repeat unchanged lines from the existing file. Examples:\n"
    "   - To add an import: `import new_module`\n"
    "   - To add a new method to a class: `    def new_method(self):\n        \"\"\"New method docstring.\"\"\"\n        pass`\n"
    "   - To change a single line: `    return new_value`\n"
    "5. If the plan step asks for an explanation or analysis, output only a Python comment explaining the error.\n"
    "6. Your response MUST end with the exact marker on its own line: `{END_OF_CODE_MARKER}`"
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
    "IMPORTANT: For new Python functions, methods, or classes, if you are generating the *full implementation* (including the body), you MUST include a comprehensive PEP 257 compliant docstring. Use Google-style format (Args:, Returns:, Example: sections). This is required to pass automated ethical and style checks.\n"
    "If only defining a signature or placeholder (e.g., `def foo(): pass`), a docstring is not required for *that specific step* but must be added in a subsequent step."
)
PYTHON_CREATION_KEYWORDS = [
    "implement function", "add method", "create class", "define function",
    "write function", "write method", "write class",
    "implement a function", "add a method", "create a class", "define a function",
    "write a function", "write a method", "a class",
    "new function", "new method", "new class", "generate function",
    "generate method", "generate class", "add function to", "add method to", "add class to",
    "write a new function", "write a python function", "write a new python function",
    "create a new function", "create a python function", "create a new python function",
    "define a new function", "define a python function",
    "define a new global function",
    "define new global function",
    "define a global function",
    "define a python function",
    "define a new python function",
    "define a new python class",
    "implement a new function", "implement a python function", "implement a new python function",
    "add a new method", "add a python method", "add a new python method",
    "create a new class", "create a python class", "create a new python class",
    "define a new class", "define a python class",
    "implement a new class", "implement a python class", "implement a new python class",
    "add function", "add method", "add class", "test case",
    "develop test case", "write test method", "create test class",
    "add logic", "implement logic", "define logic",
    "refactor function", "refactor method",
    "add helper function", "implement helper function", "define helper method",
    "enhance prompt construction", "modify prompt construction",
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
    "3. The Python code snippet you generate will be directly parsed and then merged. It must be syntactically correct on its own.\n"
    "4. Your Python code snippet MUST end with the exact marker line, on its own line: `{END_OF_CODE_MARKER}`\n\n"
    "!!! CRITICAL FOCUS FOR THIS STEP !!!\n"
    "Your *sole* objective is to fulfill the 'Specific Plan Step' provided below. "
    "Do NOT attempt to implement logic from the 'Overall Task Description' at this stage. "
    "Focus *exclusively* on the 'Specific Plan Step' and output only the requested code structure.\n"
)