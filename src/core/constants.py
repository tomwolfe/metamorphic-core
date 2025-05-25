# src/core/constants.py

# File Handling Constants
MAX_READ_FILE_SIZE = 1024 * 1024  # 1 MB
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"
END_OF_CODE_MARKER = "# METAMORPHIC_END_OF_CODE_SNIPPET"

# Workflow Driver Constants
MAX_STEP_RETRIES = 2  # Allows 2 retries per step (3 attempts total)

# Coder LLM Prompt Guidelines
GENERAL_SNIPPET_GUIDELINES = (
    "1. Ensure all string literals are correctly terminated (e.g., matching quotes, proper escaping).\n"
    "2. Pay close attention to Python's indentation rules. Ensure consistent and correct internal indentation. If inserting into existing code, the snippet's base indentation should align with the insertion point if a METAMORPHIC_INSERT_POINT is present.\n"
    "3. Generate complete and runnable Python code snippets. Avoid partial statements, unclosed parentheses/brackets/braces, or missing colons.\n"
    "4. If modifying existing code, ensure the snippet integrates seamlessly and maintains overall syntactic validity."
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
)
PYTHON_CREATION_KEYWORDS = [ # Task 1.8.Y: Keywords indicating creation of new Python code structures
    "implement function", "add method", "create class", "define function",
    "write function", "write method", "write class",
    "implement a function", "add a method", "create a class", "define a function",
    "write a function", "write a method", "write a class",
    "new function", "new method", "new class", "generate function",
    "generate method", "generate class", "add function to", "add method to", "add class to",
    "write a new function", "write a python function", "write a new python function",
    "create a new function", "create a python function", "create a new python function",
    "define a new function", "define a python function", # Removed duplicate "define a new class"
    "define a new python class", # Added keyword for test case
    "implement a new function", "implement a python function", "implement a new python function",
    "add a new method", "add a python method", "add a new python method",
    "create a new class", "create a python class", "create a new python class",
    "define a new class", "define a python class",
    "implement a new class", "implement a python class", "implement a new python class",
    # These were already in constants, but ensure they are covered
    "add function", "add method", "add class"
]

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