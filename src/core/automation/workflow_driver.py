# src/core/automation/workflow_driver.py
import logging
import html
import os
import json
from pathlib import Path
import re
from unittest.mock import MagicMock # Keep MagicMock for the mock KG/Spec/Ethics in init
import subprocess
from src.core.agents.code_review_agent import CodeReviewAgent # type: ignore
from src.core.ethics.governance import EthicalGovernanceEngine
from datetime import datetime, timezone
import uuid
import builtins
import spacy
from spacy.matcher import PhraseMatcher
import ast
from typing import List, Dict, Optional, Tuple, Any, Union # Ensure Optional is imported

from src.cli.write_file import write_file
from src.core.constants import (
    CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS, CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS,
    END_OF_CODE_MARKER, GENERAL_SNIPPET_GUIDELINES, DOCSTRING_INSTRUCTION_PYTHON,
    PYTHON_CREATION_KEYWORDS, GENERAL_PYTHON_DOCSTRING_REMINDER, # Added GENERAL_PYTHON_DOCSTRING_REMINDER
    CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS,
    MAX_READ_FILE_SIZE, METAMORPHIC_INSERT_POINT, MAX_STEP_RETRIES
)
from src.core.llm_orchestration import EnhancedLLMOrchestrator

logger = logging.getLogger(__name__) # Corrected logger name
MAX_IMPORT_CONTEXT_LINES = 200

# New constant for minimal context instruction (Task 1.8.A)
CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION = (
    "You have been provided with a **targeted, minimal section** of the source file relevant to the current step. "
    "Your task is to implement the required changes within this context. "
    "Do NOT output the entire file content. Only provide the new or changed lines."
)

nlp = None
try:
    nlp = spacy.load("en_core_web_sm")
except OSError:
    logger.error("SpaCy model 'en_core_web_sm' not found. Please install it by running: python -m spacy download en_core_web_sm")

CODE_KEYWORDS = [
"add", "import", "implement", "modify", "update", "refactor", "write", "fix", "debug", "handle", "change",
"configure", "create", "test", "install", "use", "validate", "bug",
"constant", "constants", "logic",
"refactor code", "add import",
"define constants", "implement function", "modify class",
"update logic", "change variable", "add parameter", "create file", "write test",
"fix bug", "use library", "configure setting", "add method", "remove method", "add attribute", "remove attribute",
"update dependency", "install package", "debug issue", "handle error", "add validation", "change database schema",
"write script", "update configuration", "run tests", "execute tests", "verify tests", "pytest", "test suite",
"implement core logic", "constant definition",
"core logic"
]

CONCEPTUAL_KEYWORDS = [
"understand", "design", "discuss", "review", "analyze", "research", "plan", "document", "evaluate", "gather",
"propose", "coordinate", "get", "brainstorm", "investigate",
"define", "scope",
"report", "findings",
"understand requirements", "design interface", "discuss approach", "review code", "test functionality",
"document decision", "analyze problem", "plan next step", "research options", "gather feedback", "propose solution",
"evaluate alternatives", "define scope", "create plan", "coordinate with team", "get approval",
"prepare presentation", "prepare a presentation", "write report",
"brainstorm ideas", "research and identify",
"project plan", "design proposal"
]

# Define the standard docstring instruction prompt addition (Task 1.8.Y)
DOCSTRING_INSTRUCTION_PYTHON = (
"IMPORTANT: For any new Python functions, methods, or classes, "
"you MUST include a comprehensive PEP 257 compliant docstring. "
"Use Google-style format (Args:, Returns:, Example: sections). "
"This is required to pass automated ethical and style checks."
)

def classify_plan_step(step_description: str) -> str:
    """
    Classifies a plan step description as 'code' or 'conceptual' based on enhanced keyword matching
    using NLP (SpaCy PhraseMatcher) or a regex-based fallback.

    Args:
        step_description: The text description of the plan step.

    Returns:
        'code' if likely a code modification step, 'conceptual' if likely a conceptual step,
        or 'uncertain' if the classification is ambiguous or neither type of keyword is found.
    """
    step_description_lower = step_description.lower()

    if nlp is None:
        code_score = 0
        conceptual_score = 0
        for keyword in CODE_KEYWORDS:
            code_score += len(re.findall(r'\b' + re.escape(keyword.lower()) + r'\b', step_description_lower))
        for keyword in CONCEPTUAL_KEYWORDS:
            conceptual_score += len(re.findall(r'\b' + re.escape(keyword.lower()) + r'\b', step_description_lower))

        if code_score > 0 and code_score >= conceptual_score:
            return 'code'
        elif conceptual_score > 0 and conceptual_score > code_score:
            return 'conceptual'
        else:
            return 'uncertain'
    else:
        doc = nlp(step_description.lower())
        code_matcher = PhraseMatcher(nlp.vocab)
        conceptual_matcher = PhraseMatcher(nlp.vocab)
        code_patterns = [nlp(text.lower()) for text in CODE_KEYWORDS]
        conceptual_patterns = [nlp(text.lower()) for text in CONCEPTUAL_KEYWORDS]
        code_matcher.add("CODE_PATTERNS", None, *code_patterns)
        conceptual_matcher.add("CONCEPTUAL_PATTERNS", None, *conceptual_patterns)
        code_score = len(code_matcher(doc))
        conceptual_score = len(conceptual_matcher(doc))

        if code_score > 0 and code_score >= conceptual_score:
            return 'code'
        elif conceptual_score > 0 and conceptual_score > code_score:
            return 'conceptual'
        else:
            return 'uncertain'
class Context:
    def get_full_path(self, relative_path):
        if self._resolved_base_path is None:
            logger.error(f"Base path failed to resolve. Cannot resolve relative path '{relative_path}'.")
            return None
        if not isinstance(relative_path, str):
            logger.warning(f"Path validation received invalid input type: {type(relative_path)}")
            return None
        try:
            # Use Path / operator for joining, which handles separators correctly
            full_requested_path = self._resolved_base_path / relative_path
            # Change strict=True to strict=False to allow resolving paths that don't exist.
            # This is necessary for path validation logic that checks potential paths.
            resolved_path = full_requested_path.resolve(strict=False)

            # Check if the resolved path starts with the resolved base path
            # This prevents '..' traversal and absolute paths
            if not str(resolved_path).startswith(str(Path(self.base_path).resolve())): # Use self.base_path here for consistency with the check in _validate_path
                logger.warning(f"Path traversal attempt detected during resolution: {relative_path} resolved to {resolved_path}")
                return None
            return str(resolved_path)
        except FileNotFoundError:
            # Handle FileNotFoundError specifically during resolution
            # With strict=False, this block might be hit less often, but keep it.
            logger.debug(f"Path not found during resolution: '{relative_path}' relative to '{self.base_path}'.")
            return None
        except Exception as e:
            logger.error(f"Error resolving path '{relative_path}' relative to '{self.base_path}': {e}", exc_info=True)
            return None

    def __eq__(self, other):
        if not isinstance(other, Context):
            return NotImplemented
        return self.base_path == other.base_path

    def __repr__(self):
        return f"Context(base_path='{self.base_path}')"

    def __init__(self, base_path):
        self.base_path = base_path
        try:
            self._resolved_base_path = Path(self.base_path).resolve()
        except Exception as e:
            logger.error(f"Error resolving base path '{self.base_path}': {e}", exc_info=True)
            self._resolved_base_path = None
class WorkflowDriver:
    def __init__(self, context: Context):
        self.context = context
        self.tasks = []
        self._current_task_results = {}
        self.remediation_attempts = 0
        self._current_task = {}
        self.task_target_file = None
        self.remediation_occurred_in_pass = False
        self.ethical_governance_engine = EthicalGovernanceEngine()
        self._load_default_policy()
        # Instantiate EnhancedLLMOrchestrator with required mocks
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(), # Mock KnowledgeGraph
            spec=MagicMock(), # Mock FormalSpecification
            ethics_engine=self.ethical_governance_engine
        )
        self.code_review_agent = CodeReviewAgent()
        self.logger = logger

    def _is_simple_addition_plan_step(self, plan_step_description: str) -> bool:
        """
        Determines if a plan step describes a simple, targeted addition to a file.

        Simple additions are operations like adding imports, new standalone functions,
        or specific lines, which typically require only minimal context from the
        target file for the LLM to process efficiently. This heuristic helps
        the WorkflowDriver decide when to attempt providing reduced context.

        Args:
            plan_step_description: The description of the plan step.

        Returns:
            True if the plan step is identified as a simple addition, False otherwise.
        """
        description_lower = plan_step_description.lower()

        simple_addition_keywords: List[str] = [
            "add import", "add new import", "insert import", "add an import",
            "add method", "add a new method", "define method", "implement method",
            "add function", "add a new function", "define function",
            "implement function", "insert line", "append line", "add line",
            "prepend line", "add constant", "add variable", "add attribute",
            "add property", "add decorator", "add test", "add docstring",
            "generate docstring", "update docstring", "add comment",
            "add logging", "add print statement", "add return statement",
            "add if statement", "add loop", "add try-except", "add enum",
            "add dataclass", "add type hint", "update type hint",
            "add __init__", "add __str__", "add __repr__", "add __eq__",
            "add __hash__", "define constant", # Added for Task 1.8.A
            "define new constant", # Added for more specific constant definition
            "define a new constant", # Covers test case with 'a' between define and new
            "insert into file", "append to file", "prepend to file",
            "add entry to", "add item to list",
            # Added for more robust simple addition detection (Task 1.8.A)
            "append",
            "add a type hint",
            "add a comment",
            "add a new test case",
        ]
        general_addition_patterns: List[str] = [
            "add new", "insert new", "define new", "create new",
            "append to", "prepend to",
        ]

        class_creation_specific_keywords: List[str] = [
            "add class", "add a new class", "define class", "create class"
        ]

        for keyword in simple_addition_keywords:
            if keyword in description_lower:
                if keyword in class_creation_specific_keywords:
                    msg = (f"Step '{plan_step_description[:50]}...' involves class creation keyword '{keyword}' and is not simple.")
                    self.logger.debug(msg)
                    continue
                self.logger.debug(
                    f"Step '{plan_step_description[:50]}...' identified by "
                    f"keyword: '{keyword}'"
                )
                # This is the line that should have been hit for "Define a new constant MAX_RETRIES = 3"
                return True

        for pattern in general_addition_patterns:
            if pattern in description_lower:
                if "class" in description_lower and any(
                    cls_kw in pattern for cls_kw in ["add", "new", "create", "define"]
                ):
                    msg = (f"Step '{plan_step_description[:50]}...' matches '{pattern}' and includes class; is not simple.")
                    self.logger.debug(msg)
                    continue
                self.logger.debug(
                    f"Step '{plan_step_description[:50]}...' identified by "
                    f"pattern: '{pattern}'"
                )
                return True

        self.logger.debug(
            f"Step '{plan_step_description[:50]}...' not identified as simple."
        )
        return False

    def _clean_llm_snippet(self, snippet: Optional[str]) -> str:
        """
        Cleans a snippet generated by an LLM by robustly removing common markdown fences,
        stripping leading/trailing whitespace, and respecting an end-of-code marker.
        Handles None/non-string input.
        """
        if not isinstance(snippet, str):
            self.logger.warning(f"Snippet cleaning received non-string input: {type(snippet)}. Returning empty string.")
            return ""

        processed_snippet = snippet.strip()

        # 1. Attempt to extract content from markdown fences first (case-insensitive for language tag)
        # Use re.search to find the first occurrence of a fenced block anywhere in the string.
        # The regex allows optional language tag, handles both LF and CRLF newlines,
        # and makes the newline before the closing fence optional to support empty code blocks.
        # `re.DOTALL` allows `.` to match newlines within the content.
        # `re.IGNORECASE` makes the language tag match case-insensitively.
        fenced_block_match = re.search(r"```(?:\w+)?(?:\r?\n)(.*?)(?:\r?\n)?```", processed_snippet, re.DOTALL | re.IGNORECASE)
        
        fences_found = False
        if fenced_block_match:
            # If a fenced block is found, extract its content and discard everything else.
            processed_snippet = fenced_block_match.group(1).strip()
            self.logger.debug("Markdown fenced block found and content extracted.")
            fences_found = True
        else:
            # If no fenced block is found, the snippet is treated as raw code.
            self.logger.debug("No markdown fenced block found. Treating snippet as raw code.")

        # 2. Look for the end-of-code marker and truncate if found
        # This applies to the content *after* potential fence stripping.
        # The marker is the definitive end of the code snippet.
        marker_found = False
        parts = re.split(re.escape(END_OF_CODE_MARKER), processed_snippet, 1)
        if len(parts) > 1: # Marker was found
            processed_snippet = parts[0].strip()
            marker_found = True
            self.logger.debug(f"End-of-code marker found. Snippet truncated.")
        
        # 3. Fallback: If no fences were found AND no marker was found,
        #    attempt to remove trailing non-code text (LLM chatter).
        #    This is a heuristic to handle cases where the LLM doesn't adhere to output format.
        if not fences_found and not marker_found:
            lines = processed_snippet.splitlines()
            chatter_line_patterns = [
                r"^\s*(Okay, here is the refactored code snippet\.|Here is the code\.|Let me know if you need further changes\.|Please find the code below\.|This code addresses the issue\.|Some text after the code\.|Here's the updated code:)\s*$",
                r"^\s*```.*$", # Lines that start with triple backticks (if not already handled by fence stripping)
            ]
            chatter_regex = re.compile("|".join(chatter_line_patterns), re.IGNORECASE)

            first_chatter_line_index = -1
            for i, line in enumerate(lines):
                if chatter_regex.match(line):
                    first_chatter_line_index = i
                    self.logger.debug(f"Identified first chatter line: '{line.strip()}' at index {i}. Truncating snippet.")
                    break
            
            if first_chatter_line_index != -1:
                processed_snippet = "\n".join(lines[:first_chatter_line_index])
                self.logger.debug(f"Truncated snippet based on first chatter line heuristic.")
            else:
                self.logger.debug(f"No clear chatter lines found in raw snippet. Keeping as is.")

        # 4. Final strip to remove any remaining leading/trailing whitespace
        return processed_snippet.strip()

    def _load_default_policy(self):
        # Use context.get_full_path to resolve the policy path safely
        default_policy_path = self.context.get_full_path("policies/policy_bias_risk_strict.json")
        if default_policy_path:
            try:
                # Use builtins.open explicitly
                with builtins.open(default_policy_path, 'r') as f:
                    self.default_policy_config = json.load(f)
                logger.info(f"Loaded default ethical policy: {self.default_policy_config.get('policy_name')}")
            except FileNotFoundError:
                # Log the resolved path, not the relative one
                logger.warning(f"Default ethical policy file not found at {default_policy_path}. Ethical analysis will be skipped.")
                self.default_policy_config = None
            except json.JSONDecodeError:
                # Log the resolved path
                logger.error(f"Invalid JSON in default ethical policy file: {default_policy_path}. Ethical analysis will be skipped.")
                self.default_policy_config = None
            except Exception as e:
                # Log the resolved path
                logger.error(f"Failed to load default ethical policy from {default_policy_path}: {e}", exc_info=True)
                self.default_policy_config = None
        else:
            logger.warning("Could not resolve path for default ethical policy. Ethical analysis may be impacted.")
            self.default_policy_config = None

    def start_workflow(self, roadmap_path: str, output_dir: str, context: Context):
        self.roadmap_path = roadmap_path
        self.output_dir = output_dir
        self.context = context
        try:
            # Use context.get_full_path to resolve the roadmap path safely
            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
            if full_roadmap_path is None:
                # Log the original path that failed resolution
                logger.error(f"Invalid roadmap path provided: {self.roadmap_path}. Cannot start autonomous loop.")
                return
            self.tasks = self.load_roadmap(full_roadmap_path)
        except Exception as e:
            # Log the original path that failed resolution
            logger.error(f"Failed to load roadmap from {self.roadmap_path}: {e}", exc_info=True)
            return
        logger.info(f"Workflow initiated with roadmap: {roadmap_path}, output: {output_dir}")
        self.autonomous_loop()

    def _is_add_imports_step(self, step_description: str) -> bool:
        step_lower = step_description.lower()
        import_keywords = ["add import", "import statement", "import module", "import library", "include import"]
        return any(keyword in step_lower for keyword in import_keywords)

    def _find_import_block_end(self, lines: List[str]) -> int:
        last_import_line = -1
        for i, line in enumerate(lines):
            stripped_line = line.strip()
            if stripped_line.startswith("import ") or stripped_line.startswith("from "):
                last_import_line = i
            elif stripped_line and not stripped_line.startswith("#") and last_import_line > -1:
                return i
        if last_import_line > -1:
            return len(lines)
        return 0

    def _validate_path(self, relative_path: str) -> Optional[str]:
        """
        Validates that the requested relative path resolves safely within the context's base path.
        Returns the resolved absolute path string if safe, None otherwise.
        """
        # Removed 'or not relative_path' check to allow empty string paths ("")
        if not isinstance(relative_path, str):
            self.logger.warning(f"Path validation received invalid input type: {type(relative_path)}")
            return None

        # Use context.get_full_path for the actual safety check and resolution
        # This method already handles traversal checks and logging warnings/errors.
        # It also handles empty string paths by resolving to the base path.
        resolved_path = self.context.get_full_path(relative_path) # type: ignore

        # We just return the result. Also, ensure the logger is used correctly.
        return resolved_path

    def _get_context_type_for_step(self, step_description: str) -> Optional[str]:
        """
        Identifies the type of context needed based on the step description.
        Uses stricter regex for class/method detection and defaults to None for ambiguity.
        Returns: "add_import", "add_method_to_class", "add_global_function", or None.
        """
        step_lower = step_description.lower()
        
        # Match import-related steps
        # Broaden keywords for import detection (Qwen's suggestion adapted)
        if any(kw in step_lower for kw in ["add import", "new import", "import module", "import library", 
                                            "add some imports", "add an import", "add imports"]):
            return "add_import"
        
        # Match method additions to specific classes using stricter regex (Qwen's suggestion)
        # (?!\w) is a negative lookahead asserting that the character immediately following \w+ is not a word character.
        match_method_class = re.search(r"(?:add|new|implement)\s+method\s+(?:.*?)(?:to|in)\s+(?:an\s+existing\s+class\s+called\s+|class\s+)?(\w+)(?!\w)", step_lower)
        if match_method_class:
            return "add_method_to_class"

        if any(kw in step_lower for kw in PYTHON_CREATION_KEYWORDS if "function" in kw or "method" in kw or "class" in kw) and \
           not match_method_class and \
           not any(kw in step_lower for kw in ["add import", "new import", "import module", "import library", "add some imports", "add an import", "add imports"]): # Avoid double-counting
            # More generic function/class creation if not specifically adding to a class
            # "Refactor" or "define" a function/method might imply modification, not new creation.
            # If it's explicitly about creating a new class, it might need broader context for now.
            if "class" in step_lower: # If it's about adding a class, it's likely top-level or needs broader context
                return None # Fallback to full context for new class definitions for now
            return "add_global_function" # For adding a new global function or method to an implicitly known class

        # For "refactor" or general modifications, default to full context for now.
        logger.debug(f"Could not determine specific context type for step: '{step_description}'. Defaulting to full context.")
        return None # Default to full context for ambiguous steps or modifications not yet covered

    def _extract_targeted_context(self, file_path: str, file_content: str, context_type: Optional[str], step_description: str) -> Tuple[str, bool]:
        """
        Extracts a targeted (minimal) context from file_content based on context_type.
        Returns: (context_string, is_minimal_context_bool)
        """
        if not context_type or not file_path.endswith(".py"):
            return file_content, False # Return full content if not a known type or not Python

        lines = file_content.splitlines()
        tree = None
        try:
            tree = ast.parse(file_content)
        except SyntaxError:
            logger.warning(f"SyntaxError parsing {file_path} for targeted context extraction. Falling back to full content.")
            return file_content, False

        if context_type == "add_import":
            # AST nodes for top-level imports (level=0 for direct imports in the current file)
            import_nodes = [n for n in ast.walk(tree) if isinstance(n, (ast.Import, ast.ImportFrom)) and getattr(n, 'level', 0) == 0]
            if import_nodes:
                min_line = min(n.lineno for n in import_nodes) # 1-indexed
                # Use end_lineno if available (for multi-line imports), otherwise lineno
                max_line_node = max(import_nodes, key=lambda n: n.end_lineno if hasattr(n, 'end_lineno') and n.end_lineno is not None else n.lineno)
                max_line = max_line_node.end_lineno if hasattr(max_line_node, 'end_lineno') and max_line_node.end_lineno is not None else max_line_node.lineno # 1-indexed
                
                # Buffer: 1 line before first import, 2 lines after last (to catch trailing comments/blank lines)
                start_idx = max(0, min_line - 2) # Convert to 0-indexed and add buffer
                end_idx = min(len(lines), max_line + 2)  # Convert to 0-indexed slice end and add buffer (Qwen's suggestion adapted)
                logger.debug(f"Extracting import context for {file_path}: lines {start_idx+1} to {end_idx}.")
                return "\n".join(lines[start_idx:end_idx]), True
            else: # No existing imports, take top N lines as context for new imports
                logger.debug(f"No existing imports in {file_path}. Providing top {MAX_IMPORT_CONTEXT_LINES} lines for new import context.")
                return "\n".join(lines[:MAX_IMPORT_CONTEXT_LINES]), True

        elif context_type == "add_method_to_class":
            # Regex to find class name from step description (e.g., "add method X to class Y")
            class_name_match = re.search(r"class\s+(\w+)(?!\w)", step_description, re.IGNORECASE)
            # Updated regex to match more flexible patterns for class name extraction
            class_name_match = re.search(r"(?:to|in)\s+(?:an\s+existing\s+class\s+called\s+|class\s+)?(\w+)(?!\w)", step_description, re.IGNORECASE)
            if class_name_match:
                target_class_name = class_name_match.group(1)
                for node in ast.walk(tree):
                    if isinstance(node, ast.ClassDef) and node.name == target_class_name:
                        # Buffer: 1 line before class def, 1 line after (Qwen's suggestion adapted)
                        start_idx = max(0, node.lineno - 5) # Increase buffer to include more lines before class
                        class_end_lineno = node.end_lineno if hasattr(node, 'end_lineno') and node.end_lineno is not None else node.lineno
                        end_idx = min(len(lines), class_end_lineno + 1) # Convert to 0-indexed slice end and add buffer
                        logger.debug(f"Extracting class context for '{target_class_name}' in {file_path}: lines {start_idx+1} to {end_idx}.")
                        return "\n".join(lines[start_idx:end_idx]), True
            logger.warning(f"Could not find class for 'add_method_to_class' in {file_path} from step: {step_description}. Falling back to full content.")

        # Fallback for other types or if specific extraction fails
        logger.debug(f"No specific context extraction rule for type '{context_type}' or extraction failed for {file_path}. Using full content.")
        return file_content, False

    def _determine_single_target_file(self, step_description: str, task_target_file_spec: Optional[str], prelim_flags: Dict) -> Optional[str]:
        """
        Determines a single target file (relative path) from a task's target_file list
        based on the step description, primarily for code-generation, test-writing, or
        explicit file writing steps with multiple task targets.

        Args:
            current_step_description: The text description of the plan step.
            task_target_file_spec: The 'target_file' string from the task definition.
            prelim_flags: Preliminary classification flags for the step.

        Returns:
            The determined relative single target file path if multi-target logic applied
            and a file was chosen, or None otherwise (e.g., no targets, single target,
            or multi-target but step type not applicable for this specific logic).
        """
        determined_target_file_relative = None
        potential_task_targets = []

        if task_target_file_spec and isinstance(task_target_file_spec, str):
            potential_task_targets = [f.strip() for f in task_target_file_spec.split(',') if f.strip()]

        is_code_generation_step = prelim_flags.get('is_code_generation_step_prelim', False)
        is_test_writing_step = prelim_flags.get('is_test_writing_step_prelim', False)
        is_explicit_file_writing_step = prelim_flags.get('is_explicit_file_writing_step_prelim', False)

        should_apply_multi_target_logic = is_code_generation_step or is_test_writing_step or is_explicit_file_writing_step

        if len(potential_task_targets) > 1 and should_apply_multi_target_logic:
            logger.debug(
                f"Task has multiple target files: {potential_task_targets}. Applying multi-target selection "
                f"for step: '{step_description}' (via _determine_single_target_file)"
            )
            found_in_step_description = False
            step_desc_lower = step_description.lower()

            for file_candidate_relative in potential_task_targets:
                normalized_candidate_path_str = Path(file_candidate_relative).as_posix().lower()
                filename_candidate_lower = Path(file_candidate_relative).name.lower()

                if normalized_candidate_path_str in step_desc_lower:
                    determined_target_file_relative = file_candidate_relative
                    logger.info(
                        f"Step description explicitly mentions '{determined_target_file_relative}' "
                        f"from task target list {potential_task_targets} (via _determine_single_target_file)."
                    )
                    found_in_step_description = True
                    break
                # Adjust regex lookbehind and lookahead to exclude '.' from forbidden characters
                # This allows matching filenames followed by punctuation like '.'
                # The original regex was correct, just ensuring it's used here.
                elif re.search(r'(?<![a-zA-Z0-9_-])' + re.escape(filename_candidate_lower) + r'(?![a-zA-Z0-9_-])', step_desc_lower):
                    determined_target_file_relative = file_candidate_relative
                    logger.info(
                        f"Step description explicitly mentions filename '{filename_candidate_lower}' "
                        f"(from '{determined_target_file_relative}') from task target list {potential_task_targets} (via _determine_single_target_file)."
                    )
                    found_in_step_description = True
                    break

            if not found_in_step_description:
                determined_target_file_relative = potential_task_targets[0]
                logger.warning(
                    f"Step description '{step_description}' does not explicitly mention any file "
                    f"from the task's target list: {potential_task_targets}. "
                    f"Defaulting to the first file: '{determined_target_file_relative}' (via _determine_single_target_file)."
                )
            return determined_target_file_relative # This will be a string path

        # If the above multi-target logic didn't apply (e.g., single target, no targets, or not relevant step type)
        # return None to indicate that _resolve_target_file_for_step should use its fallback.
        return None


    def _resolve_target_file_for_step(self, current_step_description: str, task_target_file_spec: Optional[str], prelim_flags: Dict) -> Optional[str]:
        """
        Determines the single target file for the current step, considering task targets,
        step type (code gen, test writing), and mentions in the step description.
        Uses _validate_path for safety.

        Args:
            current_step_description: The text description of the plan step.
            task_target_file_spec: The 'target_file' string from the task definition,
                                   which might be a single file or comma-separated list.
            prelim_flags: Preliminary classification flags for the step.

        Returns:
            The resolved single target file path for the step (absolute and safe), or None.
        """
        determined_target_file_relative = None

        # Attempt to determine the target using the specialized multi-target logic first.
        # _determine_single_target_file will handle parsing task_target_file_spec internally
        # and apply its logic if conditions (multiple targets, specific step type) are met.
        # It returns a relative path string if it makes a choice, otherwise None.
        multi_target_choice = self._determine_single_target_file(
            current_step_description,
            task_target_file_spec, # Pass the raw spec string
            prelim_flags
        )

        if multi_target_choice is not None:
            determined_target_file_relative = multi_target_choice
        else:
            # Fallback logic if _determine_single_target_file did not apply or returned None.
            # This covers:
            # 1. Single target in task_target_file_spec.
            # 2. Multi-targets but not a code_gen/test_write/explicit_write step (handled by _d_s_t_f returning None).
            # 3. No task_target_file_spec or it's empty.
            logger.debug(
                f"_determine_single_target_file did not apply or returned None. "
                f"Falling back to _determine_filepath_to_use for step: '{current_step_description}'"
            )

            potential_task_targets = []
            if task_target_file_spec and isinstance(task_target_file_spec, str):
                potential_task_targets = [f.strip() for f in task_target_file_spec.split(',') if f.strip()]

            if potential_task_targets: # Task has target(s) (could be single, or multi but not handled by _d_s_t_f)
                # Use the first target from the task spec as the default for _determine_filepath_to_use
                # if no explicit mention is found in the step by _determine_filepath_to_use itself.
                # _determine_filepath_to_use handles extracting from step or using the provided task target.
                determined_target_file_relative = self._determine_filepath_to_use(
                    current_step_description,
                    task_target_file_spec, # Pass original spec string (can be multi-target)
                    prelim_flags
                )
            else: # No task_target_file_spec or it was empty after parsing.
                if task_target_file_spec is not None and task_target_file_spec.strip() != "":
                    logger.warning(f"Task target file list was unexpectedly empty after parsing '{task_target_file_spec}' for step: '{current_step_description}'")

                determined_target_file_relative = self._determine_filepath_to_use(
                    current_step_description,
                    None, # Pass None as task_target_file spec
                    prelim_flags
                )

        # Validate the determined relative path using _validate_path
        # This returns the resolved absolute path or None
        return self._validate_path(determined_target_file_relative)

    def _determine_filepath_to_use(self, step_description: str, task_target_file: str | None, preliminary_flags: dict) -> str | None:
        # This method is now primarily a fallback used by _resolve_target_file_for_step
        # It should return a *relative* path string or None.
        filepath_from_step = preliminary_flags.get('filepath_from_step')
        is_code_generation_step_prelim = preliminary_flags.get('is_code_generation_step_prelim', False)
        is_test_writing_step_prelim = preliminary_flags.get('is_test_writing_step_prelim', False)
        is_explicit_file_writing_step_prelim = preliminary_flags.get('is_explicit_file_writing_step_prelim', False)

        effective_task_target = None
        if task_target_file and isinstance(task_target_file, str):
            targets = [f.strip() for f in task_target_file.split(',') if f.strip()]
            if targets:
                effective_task_target = targets[0] # Use the first target if multi-target spec is passed here

        filepath_to_use = effective_task_target

        if is_code_generation_step_prelim and is_test_writing_step_prelim:
            explicit_test_path_in_step = None
            all_paths_in_step_matches = re.finditer(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_description, re.IGNORECASE)
            for match in all_paths_in_step_matches:
                path_candidate = match.group(1)
                if "test_" in path_candidate.lower() or "tests/" in path_candidate.lower():
                    explicit_test_path_in_step = path_candidate
                    break

            if effective_task_target and effective_task_target.endswith('.py') and \
            ("test_" in effective_task_target.lower() or "tests/" in effective_task_target.lower()):
                filepath_to_use = effective_task_target
                logger.info(f"Test writing step: Using task_target_file as it appears to be a test file '{filepath_to_use}'.")
            elif explicit_test_path_in_step:
                filepath_to_use = explicit_test_path_in_step
                logger.info(f"Test writing step: Using explicit test path from step '{filepath_to_use}'.")
            elif effective_task_target and effective_task_target.endswith('.py') and \
                not ("test_" in effective_task_target.lower() or "tests/" in effective_task_target.lower()):
                p = Path(effective_task_target)
                derived_test_path = Path("tests") / f"test_{p.name}"
                filepath_to_use = str(derived_test_path)
                logger.info(f"Test writing step: Derived test file path '{filepath_to_use}' from task target '{effective_task_target}'.")
            elif filepath_from_step and filepath_from_step.endswith('.py') and \
                not ("test_" in filepath_from_step.lower() or "tests/" in filepath_from_step.lower()):
                p = Path(filepath_from_step)
                derived_test_path = Path("tests") / f"test_{p.name}"
                filepath_to_use = str(derived_test_path)
                logger.info(f"Test writing step: Derived test file path '{filepath_to_use}' from first path in step '{filepath_from_step}'.")
            else:
                current_path_is_test_file = filepath_to_use and filepath_to_use.endswith('.py') and \
                                            ("test_" in filepath_to_use.lower() or "tests/" in filepath_to_use.lower())
                if not current_path_is_test_file:
                    logger.warning(f"Test writing step, but could not determine a clear test file path. Current filepath_to_use: '{filepath_to_use}'. Review step and task metadata.")
        elif filepath_to_use is None and (is_explicit_file_writing_step_prelim or is_code_generation_step_prelim) and filepath_from_step:
            filepath_to_use = filepath_from_step

        if filepath_to_use is None and (is_explicit_file_writing_step_prelim or is_code_generation_step_prelim):
            filepath_from_step_match_fallback = re.search(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_description, re.IGNORECASE)
            filepath_to_use = filepath_from_step_match_fallback.group(1) if filepath_from_step_match_fallback else None
            if filepath_to_use:
                logger.info(f"Using fallback filepath '{filepath_to_use}' extracted from step description.")

        return filepath_to_use # Return the relative path

    def _determine_write_operation_details(self, step_description: str, filepath_to_use: str | None, task_target_file: str | None, preliminary_flags: Dict) -> tuple[str | None, bool]:
        step_lower = step_description.lower()
        is_explicit_file_writing_step_prelim = preliminary_flags.get('is_explicit_file_writing_step_prelim', False)
        is_research_step_prelim = preliminary_flags.get('is_research_step_prelim', False)
        step_implies_create_new_file = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in ["create file", "generate file"])
        # Use _validate_path to get the resolved task target file path for comparison
        # Note: task_target_file here is the raw spec string, not necessarily the single resolved path.
        # We need to compare the resolved filepath_to_use against the resolved *potential* task targets.
        # Let's stick to resolving the *first* task target for the prompt context for now.
        resolved_primary_task_target = None
        if task_target_file and isinstance(task_target_file, str):
            targets = [f.strip() for f in task_target_file.split(',') if f.strip()]
            if targets:
                resolved_primary_task_target = self._validate_path(targets[0])

        is_main_python_target = (resolved_primary_task_target is not None and filepath_to_use == resolved_primary_task_target and filepath_to_use is not None and filepath_to_use.endswith('.py'))

        conceptual_define_keywords_check_prelim = ["define list", "analyze", "understand", "document decision", "identify list", "define a comprehensive list"]
        is_conceptual_step_for_main_target = is_research_step_prelim or \
                                            any(re.search(r'\b' + re.escape(kw) + r'\b', step_lower) for kw in conceptual_define_keywords_check_prelim)

        content_to_write = None
        overwrite_mode = True

        # If the step is explicitly about writing content (e.g., a placeholder file) AND we have a determined filepath_to_use
        # This covers explicit file writing steps AND code generation steps that result in a file write
        # The check `content_to_write is not None` below handles whether it's a placeholder or LLM content
        if filepath_to_use and (is_explicit_file_writing_step_prelim or preliminary_flags.get('is_code_generation_step_prelim', False)):
            # Determine content for explicit file writing steps (placeholders)
            if is_explicit_file_writing_step_prelim:
                # Check if the determined filepath_to_use is the main Python target file for the task
                if is_main_python_target:
                    if step_implies_create_new_file:
                        # If it's a "create file" step targeting the main Python file, use a Python placeholder
                        overwrite_mode = False
                        content_to_write = f"# Placeholder content for Python file for step: {step_description}"
                        logger.info(f"Using placeholder for NEW main Python target {filepath_to_use} for step: '{step_description}'.")
                    elif is_conceptual_step_for_main_target:
                        # If it's a conceptual step targeting the main Python file, skip placeholder write
                        logger.info(f"Skipping placeholder write to main Python target {filepath_to_use} for conceptual step: '{step_description}'.")
                        content_to_write = None
                    else:
                        # If it's a modification step targeting the main Python file, skip placeholder write
                        # This step should be handled by code generation later if classified as such.
                        logger.info(f"Skipping placeholder write to main Python target {filepath_to_use} for modification step: '{step_description}'. This step should be handled by code generation.")
                        content_to_write = None
                else:
                    # If it's an explicit file writing step, but NOT the main Python target
                    if step_implies_create_new_file:
                        overwrite_mode = False # Don't overwrite if it's a 'create' step
                    # Use a generic placeholder, Python-specific if it's a .py file
                    if filepath_to_use.endswith('.py'):
                        content_to_write = f"# Placeholder content for Python file for step: {step_description}"
                    else:
                        content_to_write = f"// Placeholder content for step: {step_description}"
                    if content_to_write:
                        logger.info(f"Using placeholder content for file: {filepath_to_use} with overwrite={overwrite_mode}")
            # If it's a code generation step, content_to_write remains None initially.
            # The LLM-generated snippet will be used later in the autonomous loop.

        return content_to_write, overwrite_mode

    def file_exists(self, path: str) -> bool:
        """
        Checks if a file exists at the given path relative to the base path,
        ensuring the path is within the allowed context.
        """
        if not isinstance(path, str):
            logger.warning(f"file_exists received non-string input: {type(path)}")
            return False
        # Use _validate_path to get the resolved path
        resolved_path = self._validate_path(path)
        if resolved_path is None:
            # _validate_path logs a warning if resolution fails
            return False
        try:
            resolved_path_obj = Path(resolved_path)
            return resolved_path_obj.exists() and resolved_path_obj.is_file()
        except Exception as e:
            logger.error(f"Error checking existence of file {path} (resolved: {resolved_path}): {e}", exc_info=True)
            return False

    def list_files(self, path: str = "") -> List[Dict]:
        """
        Lists files and directories in a given path relative to the base path,
        ensuring the path is within the allowed context and filtering unsafe names.
        Returns a list of dictionaries like [{'name': 'file.txt', 'status': 'file'}, ...].
        """
        # Use _validate_path to get the resolved base path for listing
        # _validate_path now handles empty string correctly by calling context.get_full_path("")
        resolved_base_path_str = self._validate_path(path or "")
        if resolved_base_path_str is None:
            logger.error(f"Failed to resolve base path for listing: {path or 'base path'}")
            return []

        resolved_base_path_obj = Path(resolved_base_path_str)

        try:
            if not resolved_base_path_obj.is_dir():
                logger.error(f"Base path is not a valid directory: {path or 'base path'} (resolved: {resolved_base_path_str})")
                return []
        except Exception as e:
            logger.error(f"Error checking if base path is directory {path or 'base path'} (resolved: {resolved_base_path_str}): {e}", exc_info=True)
            return []

        entries = []
        try:
            # os.listdir expects a string path, not a Path object
            for name in os.listdir(resolved_base_path_str):
                if not self._is_valid_filename(name):
                    logger.warning(f"Skipping listing of potentially unsafe filename: {name}")
                    continue

                # Join using os.path.join or Path / and convert to string for os.path calls
                entry_path_str = os.path.join(resolved_base_path_str, name)
                entry_path_obj = Path(entry_path_str)


                try:
                    if entry_path_obj.is_file():
                        entries.append({'name': name, 'status': 'file'})
                    elif entry_path_obj.is_dir():
                        entries.append({'name': name, 'status': 'directory'})
                except Exception as e:
                    logger.warning(f"Error checking status of entry {name} in {path or 'base path'} (resolved: {resolved_base_path_str}): {e}", exc_info=True)

        except PermissionError:
            logger.error(f"Permission denied when listing files in {path or 'base path'} (resolved: {resolved_base_path_str})")
            return []
        except Exception as e:
            logger.error(f"Error listing files in {path or 'base_path'} (resolved: {resolved_base_path_str}): {e}", exc_info=True)
            return []

        return entries

    def generate_user_actionable_steps(self, steps: List[str]) -> str:
        """
        Formats a list of plan steps into a user-friendly, numbered markdown list
        with checkboxes, escaping special HTML characters.
        """
        if not isinstance(steps, list):
            raise TypeError("Input 'steps' must be a list.")

        formatted_steps = []
        for i, step in enumerate(steps):
            if not isinstance(step, str):
                raise TypeError(f"Step at index {i} is not a string: {type(step)}")
            # Escape HTML characters in the step description
            escaped_step = html.escape(step)
            formatted_steps.append(f"{i + 1}. - [ ] {escaped_step}")

        return "\n".join(formatted_steps) + ("\n" if formatted_steps else "")

    def _should_add_docstring_instruction(self, step_description: str, target_filepath: Optional[str]) -> bool:
        """
        Determines if the docstring instruction should be added to the CoderLLM prompt.
        This is true if the step involves Python code generation for new structures (functions, methods, classes) in a .py file.
        """
        # 1. Check if the target file is a Python file
        if not target_filepath or not target_filepath.lower().endswith(".py"):
            return False # Not a Python file, no Python docstring needed

        # 2. Check if the step description indicates creation of new Python structures
        step_lower = step_description.lower()

        # Revert to using any() as the explicit loop didn't seem necessary
        if any(keyword in step_lower for keyword in PYTHON_CREATION_KEYWORDS):
            logger.debug(f"Docstring instruction triggered for step: '{step_description}' targeting '{target_filepath}' due to a matching keyword.")
            return True

        # Could potentially add regex checks here for patterns like "def func_name" or "class ClassName"
        # Be cautious to avoid matching modifications of existing structures.
        # For now, relying on explicit creation keywords is safer.

        return False # No creation keyword found

    def autonomous_loop(self):
        if not hasattr(self, 'roadmap_path') or (self.roadmap_path is None):
            logger.error("Roadmap path not set. Cannot start autonomous loop.")
            return

        while True:
            logger.info('Starting autonomous loop iteration')
            self._current_task_results = {}
            self._current_task_results['step_errors'] = []
            self.remediation_attempts = 0
            self._current_task = {}
            self.task_target_file = None
            self.remediation_occurred_in_pass = False

            try:
                # Use context.get_full_path to resolve the roadmap path safely
                full_roadmap_path = self.context.get_full_path(self.roadmap_path)
                if full_roadmap_path is None:
                    # Log the original path that failed resolution
                    logger.error(f"Invalid roadmap path provided: {self.roadmap_path}. Cannot continue autonomous loop.")
                    break
                self.tasks = self.load_roadmap(full_roadmap_path)
            except Exception as e:
                # Log the original path that failed resolution
                logger.error(f"Failed to reload roadmap from {self.roadmap_path}: {e}", exc_info=True)
                break

            next_task = self.select_next_task(self.tasks)

            if next_task:
                task_id = next_task.get('task_id', 'Unknown ID')
                logger.info(f'Selected task: ID={task_id}')
                self._current_task = next_task
                self.task_target_file = next_task.get('target_file')

                solution_plan = self.generate_solution_plan(next_task)
                logger.info(f'Generated plan: {solution_plan}')

                if solution_plan:
                    logger.info(f"Executing plan for task {task_id} with {len(solution_plan)} steps.")
                    code_written_in_iteration = False

                    task_failed_step = False

                    for step_index, step in enumerate(solution_plan):
                        step_retries = 0
                        step_succeeded = False
                        step_failure_reason = None # Store reason for failure across retries
                        retry_feedback_for_llm_prompt = None # Initialize outside try block

                        while step_retries <= MAX_STEP_RETRIES:
                            try:
                                logger.info(f"Executing step {step_index + 1}/{len(solution_plan)} (Attempt {step_retries + 1}/{MAX_STEP_RETRIES + 1}): {step}")
                                prelim_flags = self._classify_step_preliminary(step)

                                # --- Step 2: Determine the actual filepath to use for the operation ---
                                # filepath_to_use is now the resolved absolute path or None
                                # This method should handle resolving relative paths against the base_path and potentially the task_target_file.
                                # Use _resolve_target_file_for_step which handles multi-target logic
                                filepath_to_use = self._resolve_target_file_for_step(step, self.task_target_file, prelim_flags)


                                # Determine if this step involves writing content (either placeholder or LLM-generated)
                                # and the overwrite mode.
                                # Note: content_to_write will be None for code generation steps;
                                # the LLM-generated snippet will be used instead.
                                content_to_write, overwrite_mode = self._determine_write_operation_details(step, filepath_to_use, self.task_target_file, prelim_flags)
                                generated_snippet = None # Initialize generated_snippet

                                # --- Step 3: Execute actions based on step classification ---

                                if prelim_flags['is_test_execution_step_prelim']:
                                    logger.info(f"Step identified as test execution. Running tests for step: {step}")
                                    test_command = ["pytest"]
                                    test_target_path = "tests/" # Default test path relative to base_path
                                    # Determine the specific test target path if possible
                                    # Use _resolve_target_file_for_step to get the resolved path for the task target
                                    # Consider if the step description itself might contain a specific test file path.
                                    resolved_task_target = self._resolve_target_file_for_step(step, self.task_target_file, prelim_flags) # Use step context too

                                    if resolved_task_target and "test_" in Path(resolved_task_target).name.lower():
                                        # If the task target file looks like a test file, use its resolved path
                                        test_target_path = resolved_task_target
                                        logger.info(f"Running tests specifically for task target file: {test_target_path}")
                                    elif filepath_to_use and "test_" in Path(filepath_to_use).name.lower():
                                        # If _resolve_target_file_for_step found a test file path in the step, use it
                                        test_target_path = filepath_to_use
                                        logger.info(f"Running tests specifically for target file identified in step: {test_target_path}")
                                    else:
                                        # Otherwise, default to the 'tests/' directory relative to the base path
                                        # Resolve the default 'tests/' path using context
                                        resolved_default_test_path = self.context.get_full_path("tests") # Pass "tests" not "tests/"
                                        if resolved_default_test_path:
                                            test_target_path = resolved_default_test_path
                                            # Updated log message to match assertion in test_workflow_validation_execution.py
                                            logger.info(f"No specific test file identified for step or task. Running all tests in '{test_target_path}'.")
                                        else:
                                            logger.error("Could not resolve default 'tests/' path. Cannot run tests.")
                                            # Add error to task results
                                            self._current_task_results['step_errors'].append(f"Step {step_index + 1} failed: Could not resolve default test path.")
                                            raise RuntimeError("Could not resolve default test path.") # Trigger retry/failure


                                    test_command.append(test_target_path)

                                    try:
                                        # Execute tests from the base path context
                                        # Assumes execute_tests is safe and handles subprocess execution correctly.
                                        return_code, stdout, stderr = self.execute_tests(test_command, self.context.base_path)
                                        test_results = self._parse_test_results(stdout)
                                        self._current_task_results['test_results'] = test_results
                                        self._current_task_results['test_stdout'] = stdout
                                        self._current_task_results['test_stderr'] = stderr
                                        self._current_task_results['last_test_command'] = test_command
                                        self._current_task_results['last_test_cwd'] = self.context.base_path

                                        logger.info(f"Test Execution Results: Status={test_results.get('status')}, Passed={test_results.get('passed')}, Failed={test_results.get('failed')}, Total={test_results.get('total')}")
                                        # If tests fail or have errors, raise an exception to trigger step retries
                                        if test_results.get('status') == 'failed':
                                            error_msg = f"Tests failed for step: {step}. Raw stderr:\n{stderr}"
                                            logger.error(error_msg)
                                            step_failure_reason = error_msg
                                            raise RuntimeError("Tests failed for step.")
                                        elif test_results.get('status') == 'error':
                                            error_msg = f"Test execution or parsing error for step: {step}. Message: {test_results.get('message')}. Raw stderr:\n{stderr}"
                                            logger.error(error_msg)
                                            step_failure_reason = error_msg
                                            raise RuntimeError(f"Test execution or parsing error: {test_results.get('message')}")
                                        # If status is 'passed', the step succeeded.
                                        step_succeeded = True # Mark step as successful

                                    except Exception as e:
                                        # Catch any exception during command execution or test parsing
                                        error_msg = f"An unexpected error occurred during command execution or test parsing: {e}"
                                        logger.error(error_msg, exc_info=True)
                                        step_failure_reason = error_msg
                                        # Ensure test_results reflects the error state if not already set
                                        if 'test_results' not in self._current_task_results or self._current_task_results['test_results'].get('status') != 'error':
                                            self._current_task_results['test_results'] = {'status': 'error', 'passed': 0, 'failed': 0, 'total': 0, 'message': str(e)}
                                        raise e # Re-raise to trigger retry/failure

                                # Use filepath_to_use (the resolved determined target file) here
                                elif prelim_flags['is_code_generation_step_prelim'] and filepath_to_use and filepath_to_use.endswith('.py'):
                                    # This step involves generating Python code and writing it to a .py file
                                    logger.info(f"Step identified as code generation for file {filepath_to_use}. Orchestrating read-generate-merge-write.") # Log resolved path
                                    # Read existing content for context (filepath_to_use is already resolved)
                                    original_full_content = self._read_file_for_context(filepath_to_use)
                                    if original_full_content is None: # Handle read errors
                                        step_failure_reason = f"Failed to read current content of {filepath_to_use} for code generation."
                                        logger.error(step_failure_reason)
                                        raise RuntimeError(step_failure_reason)

                                    context_type = self._get_context_type_for_step(step)
                                    context_for_llm, is_minimal_context = self._extract_targeted_context(filepath_to_use, original_full_content, context_type, step)
                                    logger.debug(f"Context for LLM (is_minimal={is_minimal_context}, len={len(context_for_llm)} chars) for file {filepath_to_use}.")
                                    # Construct the Coder LLM prompt using the new helper method
                                    coder_prompt = self._construct_coder_llm_prompt(self._current_task, step, filepath_to_use, context_for_llm, is_minimal_context, retry_feedback_for_llm_prompt if step_retries > 0 else None)
                                    logger.debug("Invoking Coder LLM with prompt (first 500 chars):\n%s", coder_prompt[:500]) # Log truncated prompt
                                    generated_snippet = self._invoke_coder_llm(coder_prompt)

                                    if generated_snippet:
                                        logger.info(f"Coder LLM generated snippet (first 100 chars): {generated_snippet[:100]}...")
                                        # >>> ADD CLEANING STEP HERE <<<
                                        cleaned_snippet = self._clean_llm_snippet(generated_snippet)
                                        self.logger.debug(f"Cleaned snippet (first 100 chars): {cleaned_snippet[:100]}...")

                                        # Perform pre-write validation on the generated snippet
                                        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
                                        validation_passed = True # Assume pass initially for this attempt
                                        validation_feedback = []
                                        initial_snippet_syntax_error_details = None # Store details of initial snippet syntax error
                                        try:
                                            # Attempt to parse the snippet in isolation.
                                            # This helps catch fundamental syntax errors within the snippet itself
                                            # that are not related to its integration context (e.g., typos).
                                            ast.parse(cleaned_snippet)
                                            logger.info("Snippet AST parse check passed (isolated).")
                                        except SyntaxError as se_snippet:
                                            # If it's a SyntaxError (including IndentationError), it might be acceptable
                                            # if the snippet integrates correctly into the full file.
                                            # We will still proceed to the full file check, which is more definitive.
                                            initial_snippet_syntax_error_details = f"Initial snippet syntax check failed: {se_snippet.msg} on line {se_snippet.lineno} (offset {se_snippet.offset}). Offending line: '{se_snippet.text.strip() if se_snippet.text else 'N/A'}'"
                                            logger.warning(f"Snippet AST parse check (isolated) failed with SyntaxError: {se_snippet}. This might be acceptable if the snippet integrates correctly. Proceeding to other checks.")
                                            logger.warning(f"Failed snippet (cleaned):\n---\n{cleaned_snippet}\n---")

                                            # --- START of manual addition for task_1_8_improve_snippet_handling sub-task 1 ---
                                            try:
                                                debug_dir_name = ".debug/failed_snippets"
                                                debug_dir_path_str = self.context.get_full_path(debug_dir_name)

                                                if debug_dir_path_str:
                                                    debug_dir = Path(debug_dir_path_str)
                                                    debug_dir.mkdir(parents=True, exist_ok=True)
                                                    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
                                                    current_task_id_str = getattr(self, '_current_task', {}).get('task_id', 'unknown_task')
                                                    sanitized_task_id = re.sub(r'[^\w\-_\.]', '_', current_task_id_str)
                                                    current_step_index_str = str(locals().get('step_index', -1) + 1)

                                                    filename = f"failed_snippet_{sanitized_task_id}_step{current_step_index_str}_{timestamp}.json"
                                                    filepath = debug_dir / filename

                                                    debug_data = {
                                                        "timestamp": datetime.now().isoformat(),
                                                        "task_id": current_task_id_str,
                                                        "step_description": locals().get('step', 'Unknown Step'), # Use 'step' from loop
                                                        "original_snippet_repr": repr(generated_snippet),
                                                        "cleaned_snippet_repr": repr(cleaned_snippet),
                                                        "syntax_error_details": {
                                                            "message": se_snippet.msg,
                                                            "lineno": se_snippet.lineno,
                                                            "offset": se_snippet.offset,
                                                            "text": se_snippet.text
                                                        }
                                                    }

                                                    with builtins.open(filepath, 'w', encoding='utf-8') as f_err:
                                                        json.dump(debug_data, f_err, indent=2)
                                                    self.logger.error(f"Saved malformed snippet details (JSON) to: {filepath}")
                                                else:
                                                    self.logger.error(f"Could not resolve debug directory '{debug_dir_name}' using context. Cannot save malformed snippet details (path was None).")

                                            except Exception as write_err:
                                                self.logger.error(f"Failed to save malformed snippet details: {write_err}", exc_info=True)
                                            # --- END of manual addition ---

                                        except Exception as e: # Catches non-SyntaxError from ast.parse, or other unexpected issues
                                            validation_passed = False
                                            validation_feedback.append(f"Error during pre-write syntax validation (AST parse of snippet): {e}")
                                            logger.error(f"Error during pre-write syntax validation (AST parse of snippet): {e}", exc_info=True)
                                            logger.warning(f"Failed snippet (cleaned):\n---\n{cleaned_snippet}\n---") # Log the cleaned snippet
                                        
                                        if validation_passed and self.default_policy_config:
                                            # Ethical check on the snippet itself.
                                            # This check runs only if the snippet-level AST parse didn't throw a non-SyntaxError.
                                            try:
                                                # Call ethical analysis on the snippet
                                                ethical_results = self.ethical_governance_engine.enforce_policy(
                                                    cleaned_snippet, 
                                                    self.default_policy_config,
                                                    is_snippet=True # MODIFIED: Pass is_snippet=True
                                                )
                                                if ethical_results.get('overall_status') == 'rejected':
                                                    validation_passed = False
                                                    validation_feedback.append(f"Pre-write ethical check failed: {ethical_results}")
                                                    logger.warning(f"Pre-write ethical validation failed for snippet: {ethical_results}")
                                                else:
                                                    logger.info("Pre-write ethical validation passed for snippet.")
                                            except Exception as e:
                                                validation_passed = False
                                                validation_feedback.append(f"Error during pre-write ethical validation: {e}")
                                                logger.error(f"Error during pre-write ethical validation: {e}", exc_info=True)
                                        elif validation_passed:
                                            logger.warning("Skipping pre-write ethical validation: Default policy not loaded.")

                                        if validation_passed: # Only proceed with style/security if previous checks passed
                                            # Style/Security check on the snippet itself.
                                            try:
                                                # Call code review/security analysis on the snippet
                                                style_review_results = self.code_review_agent.analyze_python(cleaned_snippet)
                                                critical_findings = [f for f in style_review_results.get('static_analysis', []) if f.get('severity') in ['error', 'security_high']]
                                                if critical_findings:
                                                    validation_passed = False
                                                    validation_feedback.append(f"Pre-write style/security check failed: Critical findings detected.")
                                                    logger.warning(f"Pre-write style/security validation failed for snippet. Critical findings: {critical_findings}")
                                                else:
                                                    logger.info("Pre-write style/security validation passed for snippet.")
                                            except Exception as e:
                                                validation_passed = False
                                                validation_feedback.append(f"Error during pre-write style/security validation: {e}")
                                                logger.error(f"Error during pre-write style/security validation: {e}", exc_info=True)

                                        # Now, the definitive syntax check: pre-merge full file check
                                        # This runs if previous checks (ethical, style, non-SyntaxError snippet parse) passed.
                                        if validation_passed:
                                            logger.info(f"Snippet-level ethical and style checks passed (or were skipped). Proceeding to pre-merge full file syntax check for {filepath_to_use}.")

                                            try:
                                                # Create a hypothetical merged content
                                                hypothetical_merged_content = self._merge_snippet(original_full_content, cleaned_snippet)
                                                ast.parse(hypothetical_merged_content)
                                                logger.info("Pre-merge full file syntax check (AST parse) passed.")
                                                # If initial_snippet_syntax_error_details existed but full file parse passed,
                                                # it means the merge context fixed the syntax. Log this.
                                                if initial_snippet_syntax_error_details:
                                                    logger.info(f"Initial snippet had a syntax issue ('{initial_snippet_syntax_error_details}'), but it integrated correctly into the full file and passed other pre-write checks.")
                                            except SyntaxError as se_merge:
                                                validation_passed = False # Definitive syntax failure
                                                validation_feedback.append(f"Pre-merge full file syntax check failed: {se_merge.msg} on line {se_merge.lineno} (offset {se_merge.offset}). Offending line: '{se_merge.text.strip() if se_merge.text else 'N/A'}'")
                                                logger.warning(f"Pre-merge full file syntax validation failed for {filepath_to_use}: {se_merge}")
                                                logger.warning(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---")
                                                # Save debug info for merge failure too (already handled by existing logic)
                                            except Exception as e_merge: # Other errors during merge/parse
                                                validation_passed = False
                                                validation_feedback.append(f"Error during pre-merge full file syntax validation: {e_merge}")
                                                logger.error(f"Error during pre-merge full file syntax validation: {e_merge}", exc_info=True)
                                                logger.warning(f"Hypothetical merged content (cleaned):\n---\n{hypothetical_merged_content}\n---")
                                        
                                        # If any check failed (ethical, style, or definitive full-file syntax)
                                        if not validation_passed:
                                            # If there was an initial snippet syntax error, ensure it's part of the feedback
                                            if initial_snippet_syntax_error_details and not any("Initial snippet syntax check failed" in item for item in validation_feedback):
                                                validation_feedback.insert(0, initial_snippet_syntax_error_details)
                                            
                                            error_message_for_retry = f"Pre-write validation failed for snippet targeting {filepath_to_use}. Feedback: {validation_feedback}"
                                            logger.warning(error_message_for_retry)
                                            # Store the detailed feedback for the Grade Report
                                            self._current_task_results['pre_write_validation_feedback'] = validation_feedback
                                            raise ValueError(f"Pre-write validation failed: {'. '.join(validation_feedback)}")

                                        # If all checks passed, proceed to write
                                        logger.info(f"All pre-write validations passed for snippet targeting {filepath_to_use}. Proceeding with actual merge/write.")
                                        # Merge the snippet into the existing content
                                        merged_content = self._merge_snippet(original_full_content, cleaned_snippet)
                                        logger.debug("Snippet merged.")
                                        # Write the merged content to the file (filepath_to_use is already resolved)
                                        logger.info(f"Attempting to write merged content to {filepath_to_use}.")
                                        try:
                                            self._write_output_file(filepath_to_use, merged_content, overwrite=True)
                                            logger.info(f"Successfully wrote merged content to {filepath_to_use}.")
                                            code_written_in_iteration = True # Mark that code was written

                                            # Perform post-write validation on the entire file
                                            try:
                                                logger.info(f"Running code review and security scan for {filepath_to_use}...")
                                                review_results = self.code_review_agent.analyze_python(merged_content)
                                                self._current_task_results['code_review_results'] = review_results
                                                logger.info(f"Code Review and Security Scan Results for {filepath_to_use}: {review_results}")
                                            except Exception as review_e:
                                                logger.error(f"Error running code review/security scan for {filepath_to_use}: {review_e}", exc_info=True)
                                                self._current_task_results['code_review_results'] = {'status': 'error', 'message': str(review_e)}
                                                # Decide if this post-write error should fail the step or just be logged.
                                                # For now, it doesn't fail the step, but it might be desirable.

                                            if self.default_policy_config:
                                                try:
                                                    logger.info(f"Running ethical analysis for {filepath_to_use}...")
                                                    ethical_analysis_results = self.ethical_governance_engine.enforce_policy(merged_content, self.default_policy_config)
                                                    self._current_task_results['ethical_analysis_results'] = ethical_analysis_results
                                                    logger.info(f"Ethical Analysis Results for {filepath_to_use}: {ethical_analysis_results}")
                                                except Exception as ethical_e:
                                                    logger.error(f"Error running ethical analysis for {filepath_to_use}: {ethical_e}", exc_info=True)
                                                    self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': str(ethical_e)}
                                                    # Decide if this post-write error should fail the step or just be logged.
                                            else:
                                                logger.warning("Default ethical policy not loaded. Skipping ethical analysis.")
                                                self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded.'}

                                            step_succeeded = True # Mark step as successful after writing and post-checks (if post-checks aren't blocking)

                                        except FileExistsError:
                                            # This should not happen with overwrite=True, but handle defensively
                                            error_msg = f"Unexpected FileExistsError when writing merged content to {filepath_to_use} with overwrite=True."
                                            logger.error(error_msg)
                                            raise FileExistsError(error_msg) # Trigger retry/failure
                                        except Exception as e:
                                            error_msg = f"Failed to write merged content to {filepath_to_use}: {e}"
                                            logger.error(error_msg, exc_info=True)
                                            step_failure_reason = error_msg
                                            raise e # Re-raise to trigger retry/failure
                                    else:
                                        # LLM returned empty or None snippet, raise exception to trigger step retries
                                        error_message = f"Coder LLM returned empty or None snippet for step {step_index + 1}. Skipping file write."
                                        logger.warning(error_message)
                                        step_failure_reason = error_message
                                        raise ValueError(f"Coder LLM returned empty snippet for step {step_index + 1}.")

                                # Use filepath_to_use (the resolved determined target file) here
                                elif content_to_write is not None and filepath_to_use:
                                    # This step involves explicitly writing content (e.g., a placeholder file)
                                    # filepath_to_use is already the resolved absolute path
                                    logger.info(f"Step identified as explicit file writing. Processing file operation for step: {step}")
                                    logger.info(f"Attempting to write file: {filepath_to_use}.")
                                    try:
                                        self._write_output_file(filepath_to_use, content_to_write, overwrite=overwrite_mode)
                                        logger.info(f"Successfully wrote placeholder content to {filepath_to_use}.")
                                        # Note: Placeholder writes do not trigger post-write validation in the current flow.
                                        # This might need refinement in future phases.
                                    except FileExistsError:
                                        logger.warning(f"File {filepath_to_use} already exists. Skipping write as overwrite={overwrite_mode}.")
                                        # File exists and overwrite is False, this is an expected behavior, not a step failure
                                        # Continue to next step.
                                    except Exception as e:
                                        # Any other exception during write is a step failure
                                        logger.error(f"Failed to write file {filepath_to_use}: {e}", exc_info=True)
                                        step_failure_reason = f"Failed to write file {filepath_to_use}: {e}"
                                        raise e # Re-raise to trigger step retries

                                else:
                                    # Step is not identified as code generation, explicit file writing, or test execution.
                                    # Or it's a code generation step but filepath_to_use is None (e.g., path resolution failed).
                                    # Or it's an explicit file writing step but filepath_to_use is None.
                                    # In these cases, we skip agent invocation/file write for this step.
                                    # If filepath_to_use is None for a step that *should* write, it's a failure.
                                    if (prelim_flags['is_code_generation_step_prelim'] or prelim_flags['is_explicit_file_writing_step_prelim']) and filepath_to_use is None:
                                        logger.error(f"Step identified as file writing/code generation but filepath_to_use could not be determined or resolved for step: {step}")
                                        step_failure_reason = f"File path could not be determined/resolved for step {step_index + 1}."
                                        raise ValueError(step_failure_reason)
                                    else:
                                        # Updated log message to match assertion in test_workflow_reporting.py
                                        logger.info(f"Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: {step}")
                                    # If the step wasn't meant to write or generate code, it succeeded implicitly.
                                    # If it was meant to write/generate but filepath_to_use was None, the exception above handles it.


                                step_succeeded = True # If we reached here without raising an exception, the step succeeded (or was skipped appropriately)
                                break # Exit retry loop for this step

                            except Exception as e:
                                # Capture the specific error message for the next retry's prompt and for logging
                                if isinstance(e, SyntaxError):
                                    offending_line_text = e.text.strip() if e.text else "N/A"
                                    current_attempt_error_message = f"SyntaxError: {e.msg} on line {e.lineno} (offset {e.offset}). Offending line: '{offending_line_text}'"
                                elif isinstance(e, ValueError) and "Pre-write validation failed" in str(e):
                                    current_attempt_error_message = str(e) # Already detailed
                                elif isinstance(e, FileExistsError): # Catch specific errors from write
                                    current_attempt_error_message = f"FileExistsError: {str(e)}"
                                elif isinstance(e, IOError): # Catch specific errors from write
                                    current_attempt_error_message = f"IOError: {str(e)}"
                                else:
                                    current_attempt_error_message = f"{type(e).__name__}: {str(e)}"

                                logger.error(f"Step execution failed (Attempt {step_retries + 1}/{MAX_STEP_RETRIES + 1}): {step}. Error: {current_attempt_error_message}", exc_info=True)
                                self._current_task_results['step_errors'].append({
                                    'step_index': step_index + 1,
                                    'step_description': step,
                                    'error_type': type(e).__name__,
                                    'error_message': str(e), # Log the raw str(e) for detailed record
                                    'timestamp': datetime.utcnow().isoformat(),
                                    'attempt': step_retries + 1,
                                    'reason': current_attempt_error_message # Store the processed error message
                                })
                                step_retries += 1
                                if step_retries <= MAX_STEP_RETRIES:
                                    logger.warning(f"Step {step_index + 1} failed. Attempting retry {step_retries}/{MAX_STEP_RETRIES}...")
                                    retry_feedback_for_llm_prompt = current_attempt_error_message # Set for the next iteration
                                else:
                                    # Log message format matches the assertion in the test
                                    step_failure_reason = current_attempt_error_message # Set final failure reason
                                    logger.error(f"Step {step_index + 1}/{len(solution_plan)} failed after {MAX_STEP_RETRIES} retries. Last error: {step_failure_reason}")
                                    task_failed_step = True # Mark task as failed due to step failure
                                    break # Exit retry loop for this step, move to next step (or end task)

                        if task_failed_step:
                            # If any step failed after retries, mark the task as Blocked and exit the step loop
                            new_status = "Blocked"
                            # Get the last error for this specific step
                            last_error = next(
                                (err for err in reversed(self._current_task_results['step_errors'])
                                 if err['step_index'] == step_index + 1),
                                {"error_type": "UnknownError", "error_message": "No specific error logged.", "reason": "Unknown reason."}
                            )
                            # Use the specific reason if available, otherwise fallback to type and message
                            # Calculate the last error reason separately to avoid nested f-string in expression
                            last_error_reason = last_error.get('reason')
                            if last_error_reason is None:
                                # Construct the default message using a separate f-string
                                last_error_reason = f'{last_error.get("error_type", "UnknownError")}: {last_error.get("error_message", "No specific error message.")}'

                            reason_blocked = f"Step {step_index + 1} ('{step}') failed after {MAX_STEP_RETRIES + 1} attempts. Last error: {last_error_reason}"
                            logger.warning(f"Task {task_id} marked as '{new_status}'. Reason: {reason_blocked}")
                            self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                            break # Exit the step loop

                    # --- End of Step Loop ---

                    if not task_failed_step:
                        # If all steps completed without failing retries, proceed to task-level evaluation
                        logger.info("All plan steps executed successfully.")
                        logger.info("Generating Grade Report...")
                        grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                        logger.info(f"--- GRADE REPORT for Task {task_id} ---\n{grade_report_json}\n--- END GRADE REPORT ---")
                        evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                        recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                        justification = evaluation_result.get("justification", "Evaluation failed.")
                        logger.info(f"Initial Grade Report Evaluation: Recommended Action='{recommended_action}', Justification='{justification}'")

                        MAX_TASK_REMEDIATION_ATTEMPTS = 2 # Define max task-level remediation attempts
                        if recommended_action == "Regenerate Code":
                            if self.remediation_attempts < MAX_TASK_REMEDIATION_ATTEMPTS:
                                logger.info(f"Attempting automated remediation (Attempt {self.remediation_attempts + 1}/{MAX_TASK_REMEDIATION_ATTEMPTS})...")
                                self.remediation_occurred_in_pass = False # Reset flag for this remediation pass

                                # Determine the target file for remediation. Prioritize task_target_file.
                                # If task_target_file is multi-target or None, try to find the last file modified in the steps.
                                filepath_for_remediation = None
                                # Iterate through steps in reverse to find the last step that involved a file write
                                for step_idx, plan_step_desc in reversed(list(enumerate(solution_plan))):
                                    prelim_flags_rem = self._classify_step_preliminary(plan_step_desc)
                                    # Use _resolve_target_file_for_step to get the resolved path for the step
                                    step_filepath_rem = self._resolve_target_file_for_step(plan_step_desc, self.task_target_file, prelim_flags_rem)
                                    # Check if the step was intended to write/generate code AND a file path was determined/resolved
                                    if (prelim_flags_rem.get('is_code_generation_step_prelim') or prelim_flags_rem.get('is_explicit_file_writing_step_prelim')) and step_filepath_rem:
                                        filepath_for_remediation = step_filepath_rem
                                        logger.debug(f"Using file path from last file-modifying step for remediation: {filepath_for_remediation}")
                                        break # Found the last file-modifying step, break the loop

                                if not filepath_for_remediation and self.task_target_file:
                                    # If no file-modifying step found, but task has a target, try the first task target
                                    targets = [f.strip() for f in self.task_target_file.split(',') if f.strip()]
                                    if targets:
                                        filepath_for_remediation = self._validate_path(targets[0])
                                        if filepath_for_remediation:
                                            logger.debug(f"Using first task target file for remediation: {filepath_for_remediation}")
                                        else:
                                            logger.warning(f"Could not resolve first task target file '{targets[0]}' for remediation.")
                                else:
                                    logger.warning("No file-modifying step found and no task target file specified. Cannot attempt automated remediation.")


                                # If a target file for remediation was determined/resolved
                                if filepath_for_remediation:
                                    # Read the current content of the file for the remediation prompt
                                    # filepath_for_remediation is already resolved absolute path
                                    current_file_content = self._read_file_for_context(filepath_for_remediation)

                                    if current_file_content is not None:
                                        # Identify the primary failure type from the grade report
                                        failure_type = self._identify_remediation_target(grade_report_json)
                                        remediation_attempted = False
                                        remediation_success = False

                                        # Attempt remediation based on failure type
                                        if failure_type == "Test Failure":
                                            remediation_attempted = True
                                            # Pass the resolved absolute file_path to the remediation method
                                            remediation_success = self._attempt_test_failure_remediation(
                                                grade_report_json, next_task, "Test Failure Remediation", filepath_for_remediation, current_file_content
                                            )
                                            if remediation_success:
                                                logger.info("Test failure remediation successful.")
                                                self.remediation_occurred_in_pass = True # Mark that remediation occurred in this pass
                                            else:
                                                logger.warning("Test failure remediation attempt failed.")

                                        # If test remediation wasn't attempted or failed, try Code Style if applicable
                                        if not remediation_success and failure_type == "Code Style":
                                            remediation_attempted = True
                                            # Pass the resolved absolute file_path to the remediation method
                                            remediation_success = self._attempt_code_style_remediation(grade_report_json, next_task, "Code Style Remediation", filepath_for_remediation, current_file_content)
                                            if remediation_success:
                                                logger.info("Style remediation attempt seems successful (code written).")
                                                self.remediation_occurred_in_pass = True # Mark that remediation occurred in this pass
                                            else:
                                                logger.warning("Style remediation attempt failed.")

                                        # If previous remediations weren't attempted or failed, try Ethical Transparency if applicable
                                        if not remediation_success and failure_type == "Ethical Transparency":
                                            remediation_attempted = True
                                            # Pass the resolved absolute file_path to the remediation method
                                            remediation_success = self._attempt_ethical_transparency_remediation(grade_report_json, next_task, "Ethical Transparency Remediation", filepath_for_remediation, current_file_content)
                                            if remediation_success:
                                                logger.info("Ethical transparency remediation seems successful (code written).")
                                                self.remediation_occurred_in_pass = True # Mark that remediation occurred in this pass
                                            else:
                                                logger.warning("Ethical transparency remediation attempt failed.")

                                        # After attempting remediation, re-generate and re-evaluate the grade report
                                        # ONLY if remediation was attempted AND resulted in a file write (signaled by remediation_success)
                                        if remediation_attempted and remediation_success:
                                            self.remediation_attempts += 1 # Increment task-level remediation counter
                                            logger.info(f"Remediation attempt {self.remediation_attempts} completed. Re-generating and re-evaluating grade report.")
                                            # Re-generate grade report with updated validation results from remediation methods
                                            grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                                            logger.info(f"--- REVISED GRADE REPORT (After Remediation) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                            # Re-evaluate the revised grade report
                                            evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                            recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                                            justification = evaluation_result.get("justification", "Evaluation failed.")
                                            logger.info(f"Revised Grade Report Evaluation (After Remediation): Recommended Action='{recommended_action}', Justification='{justification}'")
                                        elif remediation_attempted:
                                            logger.warning("Remediation attempt failed to write code. Skipping re-evaluation.")
                                        else:
                                            logger.info("No applicable automated remediation identified or attempted.")


                            else:
                                logger.warning(f"Maximum task-level remediation attempts ({MAX_TASK_REMEDIATION_ATTEMPTS}) reached for task {task_id}. Proceeding without further automated remediation.")
                                # If max attempts reached, the recommended_action from the *initial* evaluation stands.

                        # --- Determine Final Status for Task Iteration ---
                        # If task_failed_step is True, status is already set to Blocked and loop continues.
                        # Otherwise, status is based on the final evaluation result (after any remediation).
                        if not task_failed_step:
                            new_status = next_task['status'] # Start with current status
                            reason_blocked = None # Reset reason

                            if recommended_action == "Completed":
                                new_status = "Completed"
                            elif recommended_action == "Blocked":
                                new_status = "Blocked"
                                reason_blocked = justification
                            # If recommended_action is "Regenerate Code" or "Manual Review Required",
                            # the status remains "Not Started" (or whatever it was) for the next iteration
                            # unless it was explicitly set to Blocked above.

                            # Update roadmap status if it has changed
                            if new_status != next_task['status']:
                                logger.info(f"Updating task status from '{next_task['status']}' to '{new_status}' for task {task_id}")
                                self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                            else:
                                logger.info(f"Task status for {task_id} remains '{new_status}' based on evaluation.")

                else:
                    # No solution plan generated
                    logger.warning(f"No solution plan generated for task {task_id}.")
                    logger.info(f"Task {task_id} requires manual review due to failed plan generation.")
                    new_status = "Blocked"
                    reason_blocked = "Failed to generate a solution plan."
                    logger.warning(f"Task {task_id} marked as '{new_status}'. Reason: {reason_blocked}")
                    self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)

            else:
                # No tasks available in "Not Started" status
                logger.info('No tasks available in Not Started status. Exiting autonomous loop.')
                break # Exit the main autonomous loop

            logger.info('Autonomous loop iteration finished.')
        logger.info('Autonomous loop terminated.')

    def _classify_step_preliminary(self, step_description: str) -> dict:
        step_lower = step_description.lower()
        filepath_from_step_match = re.search(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_description, re.IGNORECASE)
        filepath_from_step = filepath_from_step_match.group(1) if filepath_from_step_match else None
        code_generation_verbs_prelim = ["implement", "generate code", "write function", "modify", "add", "define", "create", "update", "refactor", "write"]
        research_keywords_check_prelim = ["research and identify", "research", "analyze", "investigate", "understand"]
        code_element_keywords_check_prelim = ["import", "constant", "variable", "function", "class", "method", "definition", "parameter", "return"]
        file_writing_keywords_check_prelim = ["write", "write file", "create", "create file", "update", "update file", "modify", "modify file", "save to file", "output file", "generate file", "write output to"]
        test_execution_keywords_check_prelim = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]
        test_writing_keywords_prelim = ["write unit test", "write unit tests", "update unit test", "create test", "add test"]
        is_test_execution_step_prelim = bool(any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in test_execution_keywords_check_prelim))
        is_explicit_file_writing_step_prelim = bool(any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in file_writing_keywords_check_prelim))
        is_research_step_prelim = bool(any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in research_keywords_check_prelim))
        is_test_writing_step_prelim = bool(any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in test_writing_keywords_prelim) or \
                                    (filepath_from_step and ("test_" in filepath_from_step.lower() or "tests/" in filepath_from_step.lower())))
        is_code_generation_step_prelim = bool(not is_research_step_prelim and \
                                        any(re.search(r'\b' + re.escape(verb) + r'\b', step_lower) for verb in code_generation_verbs_prelim) and \
                                        (any(re.search(r'\b' + re.escape(element) + r'\b', step_lower) for element in code_element_keywords_check_prelim) or \
                                        (filepath_from_step and filepath_from_step.endswith('.py'))))
        return {
            "is_test_execution_step_prelim": is_test_execution_step_prelim,
            "is_explicit_file_writing_step_prelim": is_explicit_file_writing_step_prelim,
            "is_research_step_prelim": is_research_step_prelim,
            "is_test_writing_step_prelim": is_test_writing_step_prelim,
            "is_code_generation_step_prelim": is_code_generation_step_prelim,
            "filepath_from_step": filepath_from_step
        }

    def _read_file_for_context(self, full_file_path: str) -> str:
        # This method expects a full path already resolved by the caller (_resolve_target_file_for_step)
        if not isinstance(full_file_path, str) or full_file_path == "":
            logger.warning(f"Attempted to read file with invalid full path: {full_file_path}") # Log the original path passed in
            return ""
        # No need to resolve again, assume it's already resolved and validated
        full_path = full_file_path
        if not os.path.exists(full_path):
            logger.warning(f"File not found for reading: {full_file_path}") # Log the original path passed in
            return ""
        if not os.path.isfile(full_path):
            logger.warning(f"Path is not a file: {full_file_path}") # Log the original path passed in
            return ""
        try:
            file_size = os.path.getsize(full_path)
            if file_size > MAX_READ_FILE_SIZE:
                logger.warning(f"File exceeds maximum read size ({MAX_READ_FILE_SIZE} bytes): {full_file_path} ({file_size} bytes)") # Log original path
                return ""
        except Exception as e:
            logger.error(f"Error checking file size for {full_file_path}: {e}", exc_info=True) # Log original path
            return ""
        try:
            with builtins.open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            logger.debug(f"Successfully read {len(content)} characters from {full_file_path}") # Log original path
            return content
        except PermissionError:
            logger.error(f"Permission denied when reading file: {full_file_path}") # Log original path
            return ""
        except Exception as e:
            logger.error(f"Unexpected error reading file {full_file_path}: {e}", exc_info=True) # Log original path
            return ""

    def generate_solution_plan(self, task: dict) -> list[str]:
        if not isinstance(task, dict) or 'task_name' not in task or 'description' not in task:
            logger.error("Invalid task dictionary provided for plan generation.")
            return []
        task_name = task['task_name']
        description = task['description']
        task_target_file = task.get('target_file')

        # Construct the target file context section based on the task's target_file field
        target_file_prompt_section = ""
        if task_target_file:
            # Use _validate_path to get the resolved path safely
            # Note: For planning, we might want to list all targets if multi-target.
            # The current prompt template implies a single primary file.
            # Let's stick to resolving the *first* target for the prompt context for now.
            targets = [f.strip() for f in task_target_file.split(',') if f.strip()]
            if targets:
                resolved_primary_task_target_path = self._validate_path(targets[0])
                if resolved_primary_task_target_path:
                    # Construct the prompt section using the phrasing from the test assertion
                    target_file_prompt_section = (
                        f"The primary file being modified for this task is specified as `{resolved_primary_task_target_path}` "
                        "in the task metadata. Focus your plan steps on actions related to this file.\n\n"
                    )
                else:
                    logger.warning(f"Primary task target file '{targets[0]}' from spec '{task_target_file}' could not be resolved for planning prompt context.")
            else:
                logger.warning(f"Task target file spec '{task_target_file}' parsed into an empty list for planning prompt context.")


        planning_prompt = f"""You are an AI assistant specializing in software development workflows.
Your task is to generate a step-by-step solution plan for the following development task from the Metamorphic Software Genesis Ecosystem roadmap.
Please provide the plan as a numbered markdown list. Do not include any introductory or concluding remarks outside the list.

Task Name: {task_name}

Task Description:
{description}

{target_file_prompt_section}""" # Insert the new section here


        logger.debug(f"Sending planning prompt to LLM for task '{task_name}'.")
        llm_response = self._invoke_coder_llm(planning_prompt)
        if not llm_response:
            logger.warning(f"LLM returned empty response for plan generation for task '{task_name}'.")
            return []
        plan_steps = []
        step_pattern = re.compile(r'^\s*\d+\.\s*(.*)$', re.MULTILINE)
        current_step_text = None
        for line in llm_response.splitlines():
            match = step_pattern.match(line)
            if match:
                if current_step_text is not None:
                    plan_steps.append(current_step_text.strip())
                current_step_text = match.group(1).strip()
            elif current_step_text is not None:
                current_step_text += " " + line.strip()
        if current_step_text is not None:
            plan_steps.append(current_step_text.strip())
        sanitized_steps = [re.sub(r'[*_`]', '', step).strip() for step in plan_steps]
        sanitized_steps = [step for step in sanitized_steps if step]
        logger.debug(f"Parsed and sanitized plan steps: {sanitized_steps}")
        return sanitized_steps

    def _construct_coder_llm_prompt(self, task: Dict[str, Any], step_description: str, filepath_to_use: str, context_for_llm: str, is_minimal_context: bool, retry_feedback_content: Optional[str] = None) -> str:
        """
        Constructs the full prompt for the Coder LLM based on task, step, and file context,
        incorporating general, import-specific, docstring guidelines, and retry feedback.
        """
        
        preamble = "You are an expert Python Coder LLM.\n"
        if is_minimal_context:
            preamble += (
                CODER_LLM_MINIMAL_CONTEXT_INSTRUCTION + "\n" # Use the new constant
            )
        
        # Determine if this step is likely generating a full new block (function, method, class).
        # We reuse _should_add_docstring_instruction as it already identifies "new structure" generation.
        is_generating_full_block = self._should_add_docstring_instruction(step_description, filepath_to_use)

        # Define the output instructions based on whether a full block is being generated
        if is_generating_full_block:
            output_instructions = CRITICAL_CODER_LLM_FULL_BLOCK_OUTPUT_INSTRUCTIONS.format(
                END_OF_CODE_MARKER=END_OF_CODE_MARKER
            )
            # For full blocks, the "targeted modification" instructions are less relevant.
            targeted_mod_instructions_content = ""
        else:
            output_instructions = CRITICAL_CODER_LLM_OUTPUT_INSTRUCTIONS.format(
                END_OF_CODE_MARKER=END_OF_CODE_MARKER
            )
            targeted_mod_instructions_content = CODER_LLM_TARGETED_MOD_OUTPUT_INSTRUCTIONS

        import_specific_guidance_content = ""
        if self._is_add_imports_step(step_description):
            import_specific_guidance_content = (
                "\n\nSPECIFIC GUIDANCE FOR IMPORT STATEMENTS:\n"
                "You are adding import statements. Provide *only* the new import lines that need to be added. "
                "Do not repeat existing imports. Do not output any other code or explanation. "
                "Place the new imports appropriately within or after the existing import block.\n"
            )

        # Add docstring instruction conditionally
        docstring_prompt_addition = ""
        if self._should_add_docstring_instruction(step_description, filepath_to_use):
            docstring_prompt_addition = "\n" + DOCSTRING_INSTRUCTION_PYTHON + " # (e.g., 'IMPORTANT: For any new Python functions... you MUST include a comprehensive PEP 257 compliant docstring.')\n\n"
        elif filepath_to_use and filepath_to_use.lower().endswith(".py"):
            # If it's a Python file but not a clear "creation" step, add a general reminder.
            # This applies to Python source files (.py), not compiled files (.pyc) or other non-source files.
            docstring_prompt_addition = "\n" + GENERAL_PYTHON_DOCSTRING_REMINDER + "\n\n"
    
        # Add retry feedback section if provided
        retry_feedback_section = ""
        if retry_feedback_content:
            retry_feedback_section = f"--- PREVIOUS ATTEMPT FEEDBACK ---\n{retry_feedback_content}\n--- END PREVIOUS ATTEMPT FEEDBACK ---\n\n"
            retry_feedback_section += "Please review the feedback carefully and provide a corrected and improved code snippet.\n\n"

        # --- NEW: Construct target file context section ---
        target_file_prompt_section = ""
        task_target_file = task.get('target_file')
        if task_target_file:
            targets = [f.strip() for f in task_target_file.split(',') if f.strip()]
            if targets:
                resolved_primary_task_target_path = self._validate_path(targets[0])
                if resolved_primary_task_target_path:
                    target_file_prompt_section = (
                        f"The primary file being modified for this task is specified as `{resolved_primary_task_target_path}` "
                        "in the task metadata. Focus your plan steps on actions related to this file.\n\n"
                    )
        # --- END NEW SECTION ---

        # Construct the full prompt
        # Reconstructing the prompt using concatenation to avoid potential f-string multi-line issues
        coder_prompt_parts = [
            preamble,
            output_instructions, # This dynamic based on is_generating_full_block
        ]
        if targeted_mod_instructions_content: # Only add if NOT generating a full block
            coder_prompt_parts.append(targeted_mod_instructions_content)
        coder_prompt_parts.extend([
            "\n", # Newline after output instructions
            target_file_prompt_section, # Added this line back
            f"Based on the \"Specific Plan Step\" below, generate the required Python code snippet to modify the target file (`{filepath_to_use}`).\n",
            "\n", # Newline after the above line
            f"Overall Task: \"{task.get('task_name', 'Unknown Task')}\"\n",
            f"Task Description: {task.get('description', 'No description provided.')}\n",
            "\n", # Newline after task description
            retry_feedback_section, # Add retry feedback here
            "Specific Plan Step:\n",
            f"{step_description}\n",
            "\n",
            f"PROVIDED CONTEXT FROM `{filepath_to_use}` (this might be the full file or a targeted section):\n",
            "\n",
            f"{context_for_llm}\n", # Use context_for_llm here
            docstring_prompt_addition,
            import_specific_guidance_content,
            f"Key guidelines for the Python code snippet itself (these apply to the code before the {END_OF_CODE_MARKER}):\n",
            GENERAL_SNIPPET_GUIDELINES
        ])
        coder_prompt = "".join(coder_prompt_parts)


        return coder_prompt

    def _invoke_coder_llm(self, coder_llm_prompt: str) -> str:
        try:
            response = self.llm_orchestrator.generate(coder_llm_prompt)
            if response is None:
                logger.error("LLM Orchestrator generate method returned None.")
                return None
            cleaned_response = response.strip()
            if cleaned_response.startswith("```python"):
                cleaned_response = cleaned_response[len("```python"):].lstrip()
            elif cleaned_response.startswith("```"):
                cleaned_response = cleaned_response[len("```"):].lstrip()
            if cleaned_response.endswith("```"):
                cleaned_response = cleaned_response[:-len("```")].rstrip()
            return cleaned_response.strip()
        except Exception as e:
            logger.error(f"Error invoking Coder LLM: {e}", exc_info=True)
            return None

    def select_next_task(self, tasks: list) -> dict | None:
        if not isinstance(tasks, list):
            logger.warning(f"select_next_task received non-list input: {type(tasks)}")
            return None
        task_status_map = {
            task.get('task_id'): task.get('status')
            for task in tasks if isinstance(task, dict) and 'task_id' in task and 'status' in task
        }
        for task_data in tasks:
            if not isinstance(task_data, dict) or 'task_id' not in task_data or 'status' not in task_data or 'description' not in task_data or 'priority' not in task_data:
                logger.warning(f"Skipping invalid task format in list: {task_data}")
                continue
            task_id = task_data.get('task_id')
            if not self._is_valid_task_id(task_id):
                logger.warning(f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue
            task_name = task_data['task_name']
            if len(task_name) > 150:
                logger.warning(f"Task Name '{task_name}' exceeds 150 characters. Task will be skipped.")
                continue
            task_description = task_data['description']
            escaped_description = html.escape(task_description)
            depends_on = task_data.get('depends_on', [])
            if not isinstance(depends_on, list):
                logger.warning(f"Skipping task {task_id}: 'depends_on' field is not a list.")
                continue
            is_depends_on_valid = True
            validated_depends_on = []
            for dep_task_id in depends_on:
                if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                    logger.warning(f"Skipping task {task_id}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                    is_depends_on_valid = False
                    break
                validated_depends_on.append(dep_task_id)
            if not is_depends_on_valid:
                continue
            validated_task = {
                'task_id': task_id,
                'priority': task_data['priority'],
                'task_name': task_name,
                'status': task_data['status'],
                'description': escaped_description,
                'target_file': task_data.get('target_file'),
                'depends_on': validated_depends_on
            }

            if validated_task['status'] == 'Not Started':
                depends_on = validated_task.get('depends_on', [])
                all_dependencies_completed = True
                for dep_task_id in depends_on:
                    dep_status = task_status_map.get(dep_task_id)
                    if dep_status is None:
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' not found in roadmap.")
                        all_dependencies_completed = False
                        break
                    elif dep_status != 'Completed':
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' status is '{dep_status}' (requires 'Completed').")
                        all_dependencies_completed = False
                        break
                if all_dependencies_completed:
                    return validated_task
        return None

    def load_roadmap(self, roadmap_file_path):
        tasks = []
        max_file_size = 1024 * 1024
        if roadmap_file_path is None:
            logger.error(f"Failed to load roadmap from None: roadmap_file_path is None")
            return tasks
        full_roadmap_path = roadmap_file_path
        if not os.path.exists(full_roadmap_path):
            logger.error(f"ROADMAP.json file not found at path: {full_roadmap_path}")
            return tasks
        if os.path.getsize(full_roadmap_path) > max_file_size:
            logger.error(f"ROADMAP.json file exceeds maximum allowed size of {max_file_size} bytes.")
            return tasks
        try:
            # Use builtins.open explicitly
            with builtins.open(full_roadmap_path, 'r') as f:
                roadmap_data = json.load(f)
        except json.JSONDecodeError:
            logger.error(f"Invalid JSON in roadmap file: {full_roadmap_path}")
            return tasks
        if 'tasks' not in roadmap_data:
            logger.error("ROADMAP.json must contain a 'tasks' key.")
            return tasks
        if not isinstance(roadmap_data['tasks'], list):
            logger.error("'tasks' must be a list in ROADMAP.json.")
            return tasks
        for task_data in roadmap_data['tasks']:
            if not isinstance(task_data, dict):
                logger.warning(f"Skipping invalid task (not a dictionary): {task_data}")
                continue
            required_keys = ['task_id', 'priority', 'task_name', 'status', 'description']
            if not all(key in task_data for key in required_keys):
                logger.warning(f"Task missing required keys: {task_data}. Required keys are: {required_keys}")
                continue
            task_id = task_data['task_id']
            if not self._is_valid_task_id(task_id):
                logger.warning(f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue
            task_name = task_data['task_name']
            if len(task_name) > 150:
                logger.warning(f"Task Name '{task_name}' exceeds 150 characters. Task will be skipped.")
                continue
            task_description = task_data['description']
            escaped_description = html.escape(task_description)
            depends_on = task_data.get('depends_on', [])
            if not isinstance(depends_on, list):
                logger.warning(f"Skipping task {task_id}: 'depends_on' field is not a list.")
                continue
            is_depends_on_valid = True
            validated_depends_on = []
            for dep_task_id in depends_on:
                if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                    logger.warning(f"Skipping task {task_id}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                    is_depends_on_valid = False
                    break
                validated_depends_on.append(dep_task_id)
            if not is_depends_on_valid:
                continue
            task = {
                'task_id': task_id,
                'priority': task_data['priority'],
                'task_name': task_name,
                'status': task_data['status'],
                'description': escaped_description,
                'target_file': task_data.get('target_file'),
                'depends_on': validated_depends_on
            }
            tasks.append(task)
        return tasks

    def _is_valid_task_id(self, task_id):
        if not isinstance(task_id, str):
            return False
        return bool(re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9_-]*$', task_id))

    def _is_valid_filename(self, filename: str) -> bool:
        """
        Validates if a string is a safe filename (relative path component).
        Allows alphanumeric, underscore, hyphen, dot. Prevents leading/trailing dots/hyphens/underscores,
        and prevents '..' or '/' characters.
        """
        if not isinstance(filename, str) or not filename:
            return False
        if ".." in filename or "/" in filename or "\\" in filename:
            return False
        if filename.startswith('.') or filename.startswith('-') or filename.startswith('_'):
            return False
        if filename.endswith('.') or filename.endswith('-') or filename.endswith('_'):
            return False
        # Allow dots for file extensions, but not consecutive dots or dots at start/end
        if not re.fullmatch(r'^[a-zA-Z0-9_-]+(?:\.[a-zA-Z0-9_-]+)*$', filename):
            # Allow directory names without dots
            if not re.fullmatch(r'^[a-zA-Z0-9_-]+$', filename):
                return False
        return True

    def _write_output_file(self, full_filepath: str, content: str, overwrite: bool = False) -> bool:
        # This method expects a full path already resolved and validated by the caller (_resolve_target_file_for_step)
        if not isinstance(full_filepath, str) or full_filepath == "":
            logger.error(f"_write_output_file received invalid full filepath: {full_filepath}")
            return False
        try:
            # Use Path(full_filepath) directly as it's already resolved
            resolved_filepath = Path(full_filepath)
        except Exception as e:
            logger.error(f"Error creating Path object for full filepath {full_filepath} for writing: {e}", exc_info=True)
            return False

        parent_dir = resolved_filepath.parent
        # Check if parent directory exists using the resolved path object
        if not parent_dir.exists():
            try:
                # Create parent directories using the resolved path object
                parent_dir.mkdir(parents=True, exist_ok=True)
                logger.info(f"Created directory: {parent_dir}")
            except Exception as e:
                logger.error(f"Failed to create directory {parent_dir}: {e}", exc_info=True)
                return False
        try:
            # Call the imported write_file function with the resolved path string
            result = write_file(str(resolved_filepath), content, overwrite=overwrite)
            return result
        except FileExistsError as e:
            if not overwrite:
                # Re-raise if overwrite is False, this is an an expected condition
                raise e
            # Log unexpected FileExistsError if overwrite was True
            logger.error(f"Unexpected FileExistsError from write_file for {full_filepath} with overwrite=True: {e}", exc_info=True)
            return False
        except FileNotFoundError as e:
            logger.error(f"File not found error from write_file for {full_filepath}: {e}", exc_info=True)
            return False
        except PermissionError as e:
            logger.error(f"Permission error from write_file for {full_filepath}: {e}", exc_info=True)
            return False
        except Exception as e:
            logger.error(f"Unexpected error from write_file for {full_filepath}: {e}", exc_info=True)
            return False

    def execute_tests(self, test_command: list[str], cwd: str) -> tuple[int, str, str]:
        stdout = ""
        stderr = ""
        return_code = 1
        # Log the command and CWD clearly
        logger.info(f"Executing command: {' '.join(test_command)} in directory: {cwd or 'current directory'}")
        try:
            process = subprocess.run(
                test_command,
                cwd=cwd,
                capture_output=True,
                text=True,
                check=False
            )
            stdout = process.stdout
            stderr = process.stderr
            return_code = process.returncode
            if return_code == 0:
                logger.info(f"Command executed successfully. Return code: {return_code}")
            else:
                logger.error(f"Command failed with return code: {return_code}")
            logger.debug(f"STDOUT:\n{stdout}")
            logger.debug(f"STDERR:\n{stderr}")
        except FileNotFoundError:
            # Include the command and CWD in the error message
            error_msg = f"Error: Command executable '{test_command[0]}' not found or working directory '{cwd}' does not exist. Ensure '{test_command[0]}' is in your system's PATH and the working directory is valid."
            stderr = error_msg
            return_code = 127 # Standard exit code for command not found
            logger.error(error_msg)
        except Exception as e:
            # Include the command and CWD in the error message
            error_msg = f"An unexpected error occurred during command execution ('{' '.join(test_command)}' in '{cwd}'): {e}"
            stderr = error_msg
            return_code = 1
            logger.error(error_msg, exc_info=True) # Log traceback for unexpected errors
        self._current_task_results['test_stdout'] = stdout
        self._current_task_results['test_stderr'] = stderr
        self._current_task_results['last_test_command'] = test_command
        self._current_task_results['last_test_cwd'] = cwd
        return return_code, stdout, stderr

    def _get_min_indentation(self, text: str) -> int:
        """Calculates the minimum indentation of non-empty lines in a given text."""
        lines = text.splitlines()
        min_indent = float('inf')
        for line in lines:
            stripped_line = line.lstrip()
            if stripped_line: # Only consider non-empty lines
                indent = len(line) - len(stripped_line)
                min_indent = min(min_indent, indent)
        return min_indent if min_indent != float('inf') else 0 # Return 0 for empty content or all empty lines


    def _merge_snippet(self, existing_content: str, snippet: str) -> str:
        """
        Merges a snippet into existing content, applying indentation if a marker is found.
        If no marker, appends the snippet.
        """
        original_lines = existing_content.splitlines()
        # Work on a copy to avoid modifying the list while iterating if we were to use enumerate directly on lines
        lines = list(original_lines)
        marker_line_index = -1
        
        original_marker_line_indent = "" # Indentation of the line where marker is found
        line_prefix_before_marker = ""   # Content on the marker line before the marker itself (excluding original_marker_line_indent)
        line_suffix_after_marker = ""    # Content on the marker line after the marker itself

        for i, line in enumerate(lines):
            if METAMORPHIC_INSERT_POINT in line:
                marker_line_index = i
                match = re.match(r"^(\s*)", line)
                if match:
                    original_marker_line_indent = match.group(1)
                
                content_on_marker_line = line[len(original_marker_line_indent):]
                
                parts = content_on_marker_line.split(METAMORPHIC_INSERT_POINT, 1)
                if len(parts) > 0: # Ensure parts[0] exists
                    line_prefix_before_marker = parts[0]
                if len(parts) > 1:
                    line_suffix_after_marker = parts[1]
                break

        if marker_line_index != -1:
            # Marker found
            final_inserted_lines = []

            if not snippet.strip(): # Handles "", "\n", "   \n\n"
                # If snippet is empty or only contains blank lines, replace marker with its indentation/prefix/suffix.
                # If there's a prefix and no suffix, add a blank line with marker's indentation after the prefix.
                if line_prefix_before_marker.strip() and not line_suffix_after_marker.strip():
                    final_inserted_lines.append(original_marker_line_indent + line_prefix_before_marker.rstrip())
                    final_inserted_lines.append(original_marker_line_indent) # Add a blank line with marker's indentation
                else:
                    final_inserted_lines.append(original_marker_line_indent + line_prefix_before_marker + line_suffix_after_marker)
            else:
                snippet_lines = snippet.splitlines()
                
                # Add the content before the marker, if any, on its own line
                # This ensures "x = 1 # MARKER" becomes "x = 1\n    <snippet>"
                if line_prefix_before_marker.strip():
                    final_inserted_lines.append(original_marker_line_indent + line_prefix_before_marker.rstrip())
                
                # Calculate the base indentation of the snippet
                snippet_base_indent = self._get_min_indentation(snippet)
                
                # The indentation to apply to each line of the snippet is the marker's indentation
                # adjusted by the snippet's own base indentation.
                indent_to_apply_to_snippet_lines = len(original_marker_line_indent) - snippet_base_indent
                
                for s_line_content in snippet_lines:
                    if not s_line_content.strip(): # Preserve blank lines, applying marker's indentation
                        final_inserted_lines.append(original_marker_line_indent)
                    else:
                        # Calculate current indentation of the snippet line
                        current_snippet_line_indent = len(s_line_content) - len(s_line_content.lstrip())
                        # Apply the adjustment to get the new indentation
                        new_indent = current_snippet_line_indent + indent_to_apply_to_snippet_lines
                        new_indent = max(0, new_indent) # Ensure new_indent is not negative
                        final_inserted_lines.append(" " * new_indent + s_line_content.lstrip())

                # Add the content after the marker, if any, on its own line
                # This ensures "MARKER print('done')" becomes "<snippet>\n    print('done')"
                if line_suffix_after_marker.strip():
                    final_inserted_lines.append(original_marker_line_indent + line_suffix_after_marker.lstrip())
            
            lines = lines[:marker_line_index] + final_inserted_lines + lines[marker_line_index + 1:]
            return "\n".join(lines)
        else:
            # Marker not found, append logic
            # If snippet is empty and no marker, return existing content unchanged
            if not snippet:
                return existing_content

            # Otherwise, append snippet, adding a newline if existing content doesn't end with one
            if existing_content and not existing_content.endswith('\n'):
                return existing_content + "\n" + snippet
            return existing_content + snippet

    def _parse_test_results(self, raw_output: str) -> dict:
        if not raw_output:
            logger.warning("Received empty output for test results parsing.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Received empty output.'}
        # Find the last line that looks like a pytest summary line
        summary_lines = [line for line in raw_output.splitlines() if line.strip().startswith('==') and ('test session' in line or 'passed' in line or 'failed' in line or 'skipped' in line or 'error' in line)]
        if not summary_lines:
            logger.warning("Could not find pytest summary lines in output.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not find pytest summary lines in output.'}

        final_summary_line = summary_lines[-1]

        # Regex to capture counts and statuses
        counts_pattern = re.compile(r'(\d+) (passed|failed|skipped|error)')
        matches = counts_pattern.findall(final_summary_line)

        passed = 0
        failed = 0
        skipped = 0
        errors = 0
        total = 0

        # Sum up counts and calculate total
        for count_str, status_str in matches:
            try:
                count = int(count_str)
                # Total is the sum of all counts found
                total += count
                if status_str == 'passed':
                    passed = count
                elif status_str == 'failed':
                    failed = count
                elif status_str == 'skipped':
                    skipped = count
                elif status_str == 'error':
                    errors = count
            except ValueError:
                logger.warning(f"Could not parse count '{count_str}' from summary line: {final_summary_line}")
                # If parsing individual counts fails, the overall result is unreliable
                return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not parse test results output.'}


        # Determine overall status
        if failed > 0 or errors > 0:
            status = 'failed'
        elif total > 0:
            status = 'passed'
        else:
            # If total is 0 but we found a summary line, it might mean no tests were collected.
            # Treat this as passed if no failures/errors were reported, otherwise error.
            if passed == 0 and failed == 0 and skipped == 0 and errors == 0:
                status = 'error' # No counts found, unreliable output
                # Updated log message to match assertion in test_workflow_validation_execution.py
                logger.warning(f"No test results counts found or total is zero. Summary line: {final_summary_line}")
                return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not parse test results output.'}
            else: # Counts were found, but sum is 0? Unlikely, but handle.
                status = 'error' # Unreliable state
                # Updated log message to match assertion in test_workflow_validation_execution.py
                logger.warning(f"Parsed counts ({passed}p, {failed}f, {skipped}s, {errors}e) sum to {passed+failed+skipped+errors}, but total is 0. Summary line: {final_summary_line}")
                return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Inconsistent test results output.'}


        results = {
            'passed': passed,
            'failed': failed,
            'total': total,
            'status': status,
            'message': 'Parsed successfully.' if status != 'error' else 'Could not parse test results output.'
        }
        logger.debug(f"Parsed test results: {results}")
        return results


    def generate_grade_report(self, task_id: str, validation_results: dict) -> str:
        report = {
            "task_id": task_id,
            "timestamp": datetime.utcnow().isoformat(),
            "validation_results": {
                # Use .get({}, {}) to ensure these keys exist even if the outer dict is missing them
                "tests": validation_results.get('test_results', {}),
                "code_review": validation_results.get('code_review_results', {}),
                # Use the correct input key 'ethical_analysis_results'
                "ethical_analysis": validation_results.get('ethical_analysis_results', {}),
                "step_errors": validation_results.get('step_errors', []) # Ensure step_errors is always a list
            },
            "grades": self._calculate_grades(validation_results)
        }
        return json.dumps(report, indent=2)

    def _calculate_grades(self, validation_results: dict) -> dict:
        grades = {
            "non_regression": {"percentage": 0, "justification": "No valid test results available or unexpected status."}, # Default justification
            "test_success": {"percentage": 0, "justification": "No valid test results available or unexpected status."}, # Default justification
            "code_style": {"percentage": 0, "justification": "No valid code review results available or unexpected status."}, # Default justification
            "ethical_policy": {"percentage": 0, "justification": "No valid ethical analysis results available or unexpected status."}, # Default justification
            "security_soundness": {"percentage": 0, "justification": "No valid security results available or unexpected status."} # Default justification
        }

        # --- Test Success & Non-Regression ---
        # Use the correct input key 'tests'
        test_results = validation_results.get('test_results', {})
        test_status = test_results.get('status')

        if test_status == 'passed':
            total_tests = test_results.get('total', 0)
            passed_tests = test_results.get('passed', 0)
            percentage = 100 * (passed_tests / total_tests) if total_tests > 0 else 100 # 100% if 0 tests passed
            grades['test_success'] = {
                "percentage": round(percentage),
                "justification": f"Tests status: {test_status}, Passed: {passed_tests}/{total_tests}"
            }
        elif test_status == 'failed':
            total_tests = test_results.get('total', 0)
            passed_tests = test_results.get('passed', 0)
            percentage = 100 * (passed_tests / total_tests) if total_tests > 0 else 0 # 0% if 0 tests failed
            grades['test_success'] = {
                "percentage": round(percentage),
                "justification": f"Tests status: {test_status}, Passed: {passed_tests}/{total_tests}, Failed: {test_results.get('failed',0)}"
            }
        elif test_status == 'error':
            grades['test_success'] = {
                "percentage": 0,
                # Updated justification string to match assertion in test_workflow_reporting.py
                "justification": f"Test execution or parsing error: {test_results.get('message', 'Unknown error')}"
            }
        # Non-regression score is currently tied to test success
        grades['non_regression'] = {
            "percentage": grades['test_success']['percentage'],
            "justification": "Non-regression testing is currently based on Test Success percentage."
        }


        # --- Code Style & Security Soundness ---
        # Use the correct input key 'code_review'
        code_review_results = validation_results.get('code_review_results', {})
        cr_status = code_review_results.get('status')

        if cr_status == 'success' or cr_status == 'failed': # Process if analysis ran, regardless of pass/fail status
            all_findings = code_review_results.get('static_analysis', [])
            code_style_findings = [f for f in all_findings if not f.get('severity', '').startswith('security')]
            security_findings = [f for f in all_findings if f.get('severity', '').startswith('security')]

            # Code Style calculation
            high_style_issues = [f for f in code_style_findings if f.get('severity') in ['error', 'warning']]
            other_style_issues = [f for f in code_style_findings if f.get('severity') not in ['error', 'warning']]
            style_high_penalty = 15
            style_other_penalty = 3
            calculated_style_percentage = 100 - (len(high_style_issues) * style_high_penalty + len(other_style_issues) * style_other_penalty)
            style_percentage = max(0, calculated_style_percentage)
            grades['code_style'] = {
                "percentage": style_percentage,
                "justification": f"Code review status: {cr_status}, {len(code_style_findings)} style issues found."
            }

            # Security Soundness calculation
            high_security_findings = [f for f in security_findings if f.get('severity') == 'security_high']
            medium_security_findings = [f for f in security_findings if f.get('severity') == 'security_medium']
            low_security_findings = [f for f in security_findings if f.get('severity') == 'security_low']
            high_sec_penalty = 50
            medium_sec_penalty = 10
            low_sec_penalty = 2
            calculated_security_percentage = 100 - (len(high_security_findings) * high_sec_penalty +
                                                    len(medium_security_findings) * medium_sec_penalty +
                                                    len(low_security_findings) * low_sec_penalty)
            security_percentage = max(0, calculated_security_percentage)
            grades['security_soundness'] = {
                "percentage": security_percentage,
                "justification": f"Security scan status: {cr_status}, {len(security_findings)} security findings found."
            }
        elif cr_status == 'error':
            error_message = code_review_results.get('errors', {}).get('flake8', 'N/A') + ", " + code_review_results.get('errors', {}).get('bandit', 'N/A')
            # Updated justification string to match assertion in test_workflow_reporting.py
            grades['code_style'] = {"percentage": 0, "justification": f"Code review/security execution error: {error_message}"}
            # Updated justification string to match assertion in test_workflow_reporting.py
            grades['security_soundness'] = {"percentage": 0, "justification": f"Code review/security execution error: {error_message}"}


        # --- Ethical Policy ---
        # Use the correct input key 'ethical_analysis_results'
        ethical_analysis_results = validation_results.get('ethical_analysis_results', {})
        ethical_overall_status = ethical_analysis_results.get('overall_status')
        
        if ethical_overall_status == 'approved':
            grades['ethical_policy'] = {"percentage": 100, "justification": "Ethical analysis status: approved."}
        elif ethical_overall_status == 'rejected':
            grades['ethical_policy'] = {"percentage": 0, "justification": "Ethical analysis status: rejected."}
        elif ethical_overall_status == 'skipped':
            grades['ethical_policy'] = {"percentage": 0, "justification": f"Ethical analysis skipped: {ethical_analysis_results.get('message', 'Unknown reason')}."}
        elif ethical_overall_status == 'error':
            grades['ethical_policy'] = {"percentage": 0, "justification": f"Ethical analysis execution error: {ethical_analysis_results.get('message', 'Unknown error')}."}
        else: # Handle None or unexpected status
            grades['ethical_policy'] = {"percentage": 0, "justification": "No valid ethical analysis results available or unexpected status."}
        

        # --- Overall Grade ---
        # Calculate overall percentage based on weights
        overall_percentage = (
            grades['non_regression']['percentage'] * 0.20 +
            grades['test_success']['percentage'] * 0.30 +
            grades['code_style']['percentage'] * 0.10 +
            grades['ethical_policy']['percentage'] * 0.20 +
            grades['security_soundness']['percentage'] * 0.20
        )
        grades['overall_percentage_grade'] = round(overall_percentage) # Round to nearest integer

        return grades

    def _parse_and_evaluate_grade_report(self, grade_report_json: str) -> dict:
        logger.info("Parsing and evaluating Grade Report...")
        try:
            report_data = json.loads(grade_report_json)
        except json.JSONDecodeError as e:
            logger.error(f"Failed to parse Grade Report JSON: {e}", exc_info=True)
            return {"recommended_action": "Manual Review Required", "justification": f"Failed to parse Grade Report JSON: {e}"}

        grades = report_data.get('grades', {})
        validation_results = report_data.get('validation_results', {})

        overall_percentage_grade = grades.get('overall_percentage_grade', 0)
        test_results = validation_results.get('tests', {})
        code_review_results = validation_results.get('code_review', {})
        ethical_analysis_results = validation_results.get('ethical_analysis', {})
        step_errors = validation_results.get('step_errors', [])

        logger.info(f"Grade Report Metrics: Overall Grade={overall_percentage_grade}%, Test Status={test_results.get('status')}, Ethical Status={ethical_analysis_results.get('overall_status')}, Code Review Status={code_review_results.get('status')}, Step Errors={len(step_errors)}")

        recommended_action = "Manual Review Required"
        justification = "Default action for unhandled scenarios." # Step errors are handled by the main loop.
    
        # Prioritize Critical Failures (Ethical Rejection, High Security)
        if ethical_analysis_results.get('overall_status') == 'rejected':
            recommended_action = "Blocked"
            justification = "Ethical analysis rejected the code."
        elif code_review_results.get('static_analysis') and any(f.get('severity') == 'security_high' for f in code_review_results['static_analysis']):
            recommended_action = "Blocked"
            justification = "High-risk security findings detected." # Consistent with _identify_remediation_target
        # Prioritize Execution Errors (Tests, Code Review, Ethical Analysis)
        elif test_results.get('status') == 'error':
            recommended_action = "Regenerate Code" # Or Manual Review? Regenerate seems more appropriate for execution errors
            # Updated justification string to match assertion in test_workflow_reporting.py
            justification = f"Test execution or parsing error: {test_results.get('message', 'Unknown error')}."
        elif code_review_results.get('status') == 'error':
            recommended_action = "Regenerate Code" # Or Manual Review?
            # Updated justification string to match assertion in test_workflow_reporting.py
            error_message = code_review_results.get('errors', {}).get('flake8', 'N/A') + ", " + code_review_results.get('errors', {}).get('bandit', 'N/A')
            justification = f"Code review or security scan execution error: {error_message}"
        elif ethical_analysis_results.get('overall_status') == 'error':
            recommended_action = "Regenerate Code" # Or Manual Review?
            # Updated justification string to match assertion in test_workflow_reporting.py
            justification = f"Ethical analysis execution error: {ethical_analysis_results.get('message', 'Unknown error')}."
        # Prioritize Test Failures
        elif test_results.get('status') == 'failed':
            recommended_action = "Regenerate Code"
            justification = "Automated tests failed."
        # Evaluate based on Overall Grade
        elif overall_percentage_grade == 100:
            recommended_action = "Completed"
            justification = "Overall grade is 100%."
        elif overall_percentage_grade >= 80: # Threshold for automated regeneration
            recommended_action = "Regenerate Code"
            justification = f"Overall grade ({overall_percentage_grade}%) is below 100% but meets regeneration threshold."
        else: # Grade below threshold or other issues not explicitly handled
            recommended_action = "Manual Review Required"
            justification = f"Overall grade ({overall_percentage_grade}%) is below regeneration threshold or other issues require manual review."

        logger.info(f"Recommended Action: {recommended_action}. Justification: {justification}")
        return {"recommended_action": recommended_action, "justification": justification}

    def _safe_write_roadmap_json(self, roadmap_path: str, new_content: dict) -> bool:
        # Use _validate_path to get the resolved path safely
        resolved_filepath = self._validate_path(roadmap_path)
        if resolved_filepath is None:
            # _validate_path logs a warning if resolution fails
            logger.error(f"Security alert: Path traversal attempt detected for roadmap file: {roadmap_path}")
            return False
        if not isinstance(new_content, dict):
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Content is not a dictionary.")
            return False
        if 'tasks' not in new_content:
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Missing 'tasks' key.")
            return False

        resolved_filepath_obj = Path(resolved_filepath)
        roadmap_dir = resolved_filepath_obj.parent
        # Use a temporary filename that is unlikely to conflict and is in the same directory
        temp_filename = f".{resolved_filepath_obj.name}.{uuid.uuid4()}.tmp"
        temp_filepath = roadmap_dir / temp_filename

        # Clean up any leftover temporary file from a previous failed attempt
        if temp_filepath.exists():
            try:
                os.remove(temp_filepath)
                logger.debug(f"Cleaned up leftover temporary file: {temp_filepath}")
            except Exception as cleanup_e:
                logger.warning(f"Failed to clean up leftover temporary file {temp_filepath}: {cleanup_e}")

        try:
            # Use builtins.open explicitly
            with builtins.open(temp_filepath, 'w', encoding='utf-8') as f:
                json.dump(new_content, f, indent=2)

            # Atomically replace the original file with the temporary file
            os.replace(temp_filepath, resolved_filepath)

            logger.info(f"Successfully wrote updated roadmap to {roadmap_path}") # Log original path
            return True

        except (IOError, OSError, PermissionError, json.JSONDecodeError) as e:
            logger.error(f"Error writing roadmap file {roadmap_path}: {e}", exc_info=True) # Log original path
            # Attempt to clean up the temporary file if it exists after an error
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after error: {e}")
                except Exception as cleanup_e_inner:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after error: {cleanup_e_inner}")
            return False
        except Exception as cleanup_e:
            logger.error(f"Unexpected error during roadmap file write {roadmap_path}: {cleanup_e}", exc_info=True) # Log original path
            # Attempt to clean up the temporary file if it exists after an unexpected error
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after unexpected error: {cleanup_e}")
                except Exception as cleanup_e_inner:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after unexpected error: {cleanup_e_inner}")
            return False

    def _update_task_status_in_roadmap(self, task_id: str, new_status: str, reason: str = None):
        try:
            # Use context.get_full_path to resolve the roadmap path safely
            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
            if full_roadmap_path is None:
                # Log the original path that failed resolution
                logger.error(f"Cannot update roadmap status: Invalid roadmap path provided: {self.roadmap_path}")
                return

            try:
                # Use builtins.open explicitly
                with builtins.open(full_roadmap_path, 'r') as f:
                    roadmap_data = json.load(f)
            except FileNotFoundError:
                # Log the resolved path
                logger.error(f"Error updating roadmap status for task {task_id}: Roadmap file not found at {full_roadmap_path}")
                return
            except json.JSONDecodeError:
                # Log the resolved path
                logger.error(f"Error updating roadmap status for task {task_id}: Invalid JSON in roadmap file {full_roadmap_path}")
                return
            except Exception as e:
                # Log the resolved path
                logger.error(f"Error reading roadmap file {full_roadmap_path} for status update: {e}", exc_info=True)
                return

            task_found = False
            if isinstance(roadmap_data, dict) and isinstance(roadmap_data.get('tasks'), list):
                for task_entry in roadmap_data['tasks']:
                    if isinstance(task_entry, dict) and task_entry.get('task_id') == task_id:
                        old_status = task_entry.get('status', 'Unknown')
                        task_entry['status'] = new_status
                        if reason:
                            task_entry['reason_blocked'] = reason
                        elif 'reason_blocked' in task_entry:
                            del task_entry['reason_blocked']
                        logger.info(f"Updating task status from '{old_status}' to '{new_status}' for task {task_id}")
                        task_found = True
                        break

            if task_found:
                # Pass the original roadmap_path to _safe_write_roadmap_json
                if self._safe_write_roadmap_json(self.roadmap_path, roadmap_data):
                    logger.info(f"Successfully wrote updated status for task {task_id} in {self.roadmap_path}") # Log original path
                else:
                    logger.error(f"Failed to safely write updated roadmap for task {task_id}") # Log original path
            else:
                logger.warning(f"Task {task_id} not found in roadmap file {self.roadmap_path} for status update.") # Log original path

        except Exception as e:
            logger.error(f"Error updating roadmap status for task {task_id}: {e}", exc_info=True)

    def _identify_remediation_target(self, grade_report_json: str) -> str | None:
        try:
            report_data = json.loads(grade_report_json)
            grades = report_data.get('grades', {})
            validation = report_data.get('validation_results', {})

            # Prioritize Step Errors - Should be handled before remediation is attempted, but double check
            step_errors = validation.get('step_errors', [])
            if step_errors:
                logger.debug("Identified Step Errors. Remediation not applicable.")
                return None # Remediation is not the right action for step errors

            # Prioritize Critical Failures (High Security) - Ethical Rejection handled below
            code_review_results = validation.get('code_review', {})
            if code_review_results.get('static_analysis') and any(f.get('severity') == 'security_high' for f in code_review_results['static_analysis']):
                logger.debug("Identified High Security findings. Remediation not applicable (requires manual review).") # Consistent with _parse_and_evaluate_grade_report
                return None # High security issues require manual review, not automated remediation

            # Prioritize Execution Errors - Should be handled before remediation is attempted, but double check
            if validation.get('tests', {}).get('status') == 'error' or \
            code_review_results.get('status') == 'error' or \
            validation.get('ethical_analysis', {}).get('overall_status') == 'error':
                logger.debug("Identified Execution Errors. Remediation not applicable.")
                return None # Execution errors block progress, not suitable for code remediation

            # Prioritize Ethical Transparency Violation (Specific Check)
            ethical_results = validation.get('ethical_analysis', {})
            # Check if the specific TransparencyScore status is 'violation'
            transparency_status = ethical_results.get('TransparencyScore', {}).get('status')
            if transparency_status == 'violation':
                logger.debug("Identified Ethical Transparency violation as remediation target.")
                return "Ethical Transparency"

            # Prioritize Test Failure
            test_results = validation.get('tests', {})
            if test_results.get('status') == 'failed':
                logger.debug("Identified Test Failure as remediation target.")
                return "Test Failure"

            # Prioritize Code Style issues if findings exist
            # Check if code review results are available and not in error state
            if code_review_results.get('status') in ['success', 'failed']:
                all_findings = code_review_results.get('static_analysis', [])
                style_findings = [f for f in all_findings if not f.get('severity', '').startswith('security')]
                if style_findings: # Check if there are any style findings
                    logger.debug("Identified Code Style as remediation target.")
                    return "Code Style"

            logger.debug("No specific remediation target identified from grade report for automated remediation.")
            return None

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for remediation target identification.")
            return None
        except Exception as e:
            logger.error(f"Error identifying remediation target: {e}", exc_info=True)
            return None

    def _attempt_code_style_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        logger.info(f"Attempting code style remediation for {file_path}...") # Log original path
        try:
            report_data = json.loads(grade_report_json)
            code_review_results = report_data.get('validation_results', {}).get('code_review', {})
            findings = code_review_results.get('static_analysis', [])
            # Filter for style findings (severity not starting with 'security')
            style_feedback = [f"- {f.get('code')} at line {f.get('line')}: {f.get('message')}" for f in findings if not f.get('severity', '').startswith('security')]

            if not style_feedback:
                logger.warning("No specific code style feedback found to provide to LLM.")
                return False

            feedback_str = "\n".join(style_feedback)
            logger.debug(f"Extracted code style feedback:\n{feedback_str}")

            feedback_prompt = f"""You are a Coder LLM expert in Python code style (PEP 8, Flake8).
The following Python code failed automated code style checks.
File Path: {file_path}
Original Task: "{task.get('task_name', 'Unknown Task')}"
Plan Step: "{step_desc}"

Code with Issues:


{original_code}
Identified Code Style Issues (e.g., Flake8):
{feedback_str}

Your task is to rewrite the entire code block above, fixing only the identified code style issues.
Maintain all original logic and functionality.
Adhere strictly to PEP 8 guidelines.
Ensure the corrected code passes Flake8 checks based on the feedback provided.
Output only the complete, corrected Python code. Do not include explanations or markdown fences.
"""
            corrected_code = self._invoke_coder_llm(feedback_prompt)


            if not corrected_code or corrected_code.strip() == original_code.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged.")
                return False

            logger.info("LLM provided corrected code. Applying and re-validating...")
            content_to_write = corrected_code

            # Resolve file_path before writing (file_path is already resolved absolute path)
            resolved_file_path = file_path # It's already resolved

            write_success = self._write_output_file(resolved_file_path, content_to_write, overwrite=True)

            if write_success:
                try:
                    logger.info(f"Re-running code review for {file_path} after remediation...") # Log original path
                    new_review_results = self.code_review_agent.analyze_python(content_to_write)
                    self._current_task_results['code_review_results'] = new_review_results
                    logger.info(f"Code Review Results after remediation: {new_review_results}")
                    # Note: Re-validation success/failure doesn't determine the return value of this method,
                    # only whether the write was successful. The autonomous loop re-evaluates the grade report.
                except Exception as e:
                    logger.error(f"Error occurred during code review re-scan after remediation: {e}", exc_info=True)
                    self._current_task_results['code_review_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}

                return True # Remediation attempt successful if write succeeded
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.") # Log original path
                return False # Remediation attempt failed if write failed

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for code style remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during code style remediation: {e}", exc_info=True)
            return False

    def _attempt_ethical_transparency_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        logger.info(f"Attempting ethical transparency remediation for {file_path}...") # Log original path
        try:
            report_data = json.loads(grade_report_json)
            ethical_results = report_data.get('validation_results', {}).get('ethical_analysis', {})
            # Check if overall status is rejected, as _identify_remediation_target should ensure this
            # Also specifically check for TransparencyScore violation
            transparency_status = ethical_results.get('TransparencyScore', {}).get('status')
            if transparency_status != 'violation':
                logger.warning("Ethical transparency remediation triggered, but TransparencyScore status is not 'violation'.")
                return False

            # Use the details from the report, or a default message
            # Look for specific violation details if available, otherwise use a generic message
            violation_details = []
            # Iterate through all keys in ethical_results, not just policy names
            for key, policy_result in ethical_results.items():
                # Ensure policy_result is a dict and has a status key
                if isinstance(policy_result, dict) and policy_result.get('status') == 'violation':
                    details = policy_result.get('details', f"Violation in policy/check '{key}'.")
                    violation_details.append(details)

            feedback_str = "\n".join(violation_details) if violation_details else "Ethical transparency violation detected (details not available)."

            logger.debug(f"Extracted ethical transparency feedback: {feedback_str}")

            feedback_prompt = f"""You are a Coder LLM expert in Python documentation and code transparency.
The following Python code failed an automated ethical transparency check, likely due to missing docstrings or other transparency issues.
File Path: {file_path}
Original Task: "{task.get('task_name', 'Unknown Task')}"
Plan Step: "{step_desc}"

Code with Issues:


{original_code}
Identified Ethical Transparency Issue:
{feedback_str}

Your task is to rewrite the entire code block above, addressing the identified transparency issue(s).
This may involve adding comprehensive docstrings (PEP 257, Google style) to functions, methods, and classes, or adding comments where code logic is complex or potentially ambiguous.
Maintain all original logic and functionality.
Output only the complete, corrected Python code with added documentation/comments. Do not include explanations or markdown fences.
"""
            corrected_code = self._invoke_coder_llm(feedback_prompt)


            if not corrected_code or corrected_code.strip() == original_code.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged.")
                return False

            logger.info("LLM provided corrected code with docstrings. Applying and re-validating...")
            content_to_write = corrected_code

            # Resolve file_path before writing (file_path is already resolved absolute path)
            resolved_file_path = file_path # It's already resolved

            write_success = self._write_output_file(resolved_file_path, content_to_write, overwrite=True)

            if write_success:
                if self.default_policy_config:
                    try:
                        logger.info(f"Re-running ethical analysis for {file_path} after remediation...") # Log original path
                        new_ethical_results = self.ethical_governance_engine.enforce_policy(content_to_write, self.default_policy_config)
                        self._current_task_results['ethical_analysis_results'] = new_ethical_results
                        logger.info(f"Ethical Analysis Results after remediation: {new_ethical_results}")
                        # Note: Re-validation success/failure doesn't determine the return value of this method,
                        # only whether the write was successful. The autonomous loop re-evaluates the grade report.
                    except Exception as e:
                        logger.error(f"Error occurred during ethical analysis re-scan after remediation: {e}", exc_info=True)
                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': f"Re-validation error: {e}"}
                else:
                    logger.warning("Cannot re-run ethical analysis after remediation: Default policy not loaded.")
                    self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded for re-scan.'}

                return True # Remediation attempt successful if write succeeded
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.") # Log original path
                return False # Remediation attempt failed if write failed

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for ethical transparency remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during ethical transparency remediation: {e}", exc_info=True)
            return False

    def _attempt_test_failure_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        logger.info(f"Attempting test failure remediation for {file_path}...") # Log original path
        try:
            # Get test results and output from the current task results
            stdout = self._current_task_results.get('test_stdout', '')
            stderr = self._current_task_results.get('test_stderr', '')
            test_results = self._current_task_results.get('test_results', {})

            # Ensure test status is 'failed' before proceeding
            if test_results.get('status') != 'failed':
                logger.warning("Test failure remediation triggered, but test status is not 'failed'.")
                return False

            logger.debug(f"Test failure details - Stdout: {stdout}, Stderr: {stderr}")

            # Read the current file content again, in case it was modified by other steps
            # file_path is already resolved absolute path
            current_file_content = self._read_file_for_context(file_path)

            if not current_file_content:
                logger.error(f"Failed to read current file content for {file_path} during test remediation. Cannot attempt remediation.") # Log original path
                return False

            task_name = task.get('task_name', 'Unknown Task')
            task_description = task.get('description', 'No description provided')

            prompt = f"""
You are tasked with fixing the following test failure in the Python code.
Task: {task_name}
Description: {task_description}
File to modify: {file_path}

Current code content:


{current_file_content}
Test execution output:
Stdout:


{stdout}
Stderr:


{stderr}
Instructions:
Analyze the test failure output (Stdout and Stderr) and the current code content to identify the root cause of the test failures.
Generate the complete, corrected Python code for the file {file_path}. Your response should contain the entire content of the file after applying the necessary fixes.
Do NOT include any surrounding text, explanations, or markdown code block fences (```). Provide just the raw code lines that constitute the complete, corrected file content.
Maintain all original logic and functionality not related to the test failures.
Adhere to PEP 8 style guidelines.
Note: The Debug Agent (task_2_2_6) is NOT available; you must generate the fix directly based on the provided information.
Your response should be the complete, corrected code content that addresses the test failure based on the provided context and error messages.
"""
            corrected_code = self._invoke_coder_llm(prompt)


            if not corrected_code or corrected_code.strip() == current_file_content.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged for test failure remediation.")
                return False

            logger.info("LLM provided corrected code for test failure. Applying and re-validating...")
            content_to_write = corrected_code

            # Resolve file_path before writing (file_path is already resolved absolute path)
            resolved_file_path_write = file_path # It's already resolved

            write_success = self._write_output_file(resolved_file_path_write, content_to_write, overwrite=True)

            if write_success:
                logger.info(f"Successfully wrote fixed code to {file_path}") # Log original path
                try:
                    logger.info(f"Re-running validations for {file_path} after test failure remediation...") # Log original path
                    # Re-run tests
                    test_command = self._current_task_results.get('last_test_command', ['pytest', 'tests/'])
                    cwd = self._current_task_results.get('last_test_cwd', self.context.base_path)
                    return_code, new_stdout, new_stderr = self.execute_tests(test_command, cwd)
                    self._current_task_results['test_stdout'] = new_stdout
                    self._current_task_results['test_stderr'] = new_stderr
                    self._current_task_results['test_results'] = self._parse_test_results(new_stdout)

                    # Re-run code review and ethical analysis
                    code_review_result = self.code_review_agent.analyze_python(content_to_write)
                    self._current_task_results['code_review_results'] = code_review_result

                    if self.default_policy_config:
                        ethical_result = self.ethical_governance_engine.enforce_policy(content_to_write, self.default_policy_config)
                        self._current_task_results['ethical_analysis_results'] = ethical_result
                    else:
                        logger.warning("Default ethical policy not loaded. Skipping ethical analysis re-scan.")
                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded for re-scan.'}

                    logger.info(f"Validations re-run after test failure remediation.")

                except Exception as e:
                    logger.error(f"Error occurred during re-validation after test failure remediation: {e}", exc_info=True)
                    # Update results with error status if re-validation fails
                    if 'test_results' not in self._current_task_results or self._current_task_results['test_results'].get('status') != 'error':
                        self._current_task_results['test_results'] = {'status': 'error', 'passed': 0, 'failed': 0, 'total': 0, 'message': f"Re-validation error: {e}"}
                    if 'code_review_results' not in self._current_task_results or self._current_task_results['code_review_results'].get('status') != 'error':
                        self._current_task_results['code_review_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                    if 'ethical_analysis_results' not in self._current_task_results or self._current_task_results['ethical_analysis_results'].get('overall_status') != 'error':
                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': f"Re-validation error: {e}"}

                return True # Remediation attempt successful if write succeeded
            else:
                logger.error(f"Failed to write fixed code to {file_path}. Aborting test failure remediation.") # Log original path
                return False # Remediation attempt failed if write failed

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for test failure remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during test failure remediation: {e}", exc_info=True)
            return False

    def _extract_top_n_lines(self, file_content: str, n: int) -> str:
        """
        Extracts the top N lines from the given file content.

        Args:
            file_content: The full content of the file as a string.
            n: The number of lines to extract from the top.

        Returns:
            A string containing the top N lines, or the full content if N is larger
            than the total lines. Returns an empty string if n is 0 or content is empty.
        
        Example:
            content = "line1\\nline2\\nline3"
            _extract_top_n_lines(content, 2)  # Returns "line1\\nline2"
        """
        if not file_content or n <= 0:
            return ""
        lines = file_content.splitlines()
        return "\n".join(lines[:n])

    def _extract_import_block(self, file_content: str) -> str:
        """
        Extracts the import block from the given Python file content.
        The import block includes all import statements (single and multiline),
        module/file-level docstrings, shebangs, and any comments or blank lines
        interspersed at the beginning of the file, up to the first line of
        executable code (e.g., function definition, class definition, variable
        assignment not part of an import).

        Args:
            file_content: The full content of the Python file as a string.

        Returns:
            A string containing the import block. Returns an empty string if no
            relevant lines are found at the beginning or if the file content is empty.
        
        Example:
            content = "#!/usr/bin/env python\\n\\"\"\"Module doc.\"\"\"\\nimport os\\n\\n# comment\\nfrom sys import path\\ndef my_func(): pass"
            _extract_import_block(content) 
            # Returns: "#!/usr/bin/env python\\n\\"\"\"Module doc.\"\"\"\\nimport os\\n\\n# comment\\nfrom sys import path"
        """
        if not file_content:
            return ""

        lines = file_content.splitlines()
        import_block_lines = []
        in_multiline_import = False

        for line_number, line_text in enumerate(lines):
            stripped_line = line_text.strip()

            if in_multiline_import:
                import_block_lines.append(line_text)
                if ")" in stripped_line: # Simplistic check for end of multiline import
                    in_multiline_import = False
                continue

            if not stripped_line: # Blank line
                import_block_lines.append(line_text)
                continue
            
            if stripped_line.startswith("#"): # Comment
                import_block_lines.append(line_text)
                continue

            if stripped_line.startswith("\"\"\"") or stripped_line.startswith("'''"): # Docstring
                import_block_lines.append(line_text)
                # Handle multi-line docstrings - simplistic: continue until closing triple quotes
                if not (stripped_line.endswith("\"\"\"") or stripped_line.endswith("'''")) or len(stripped_line) < 6 :
                    for next_line_idx in range(line_number + 1, len(lines)):
                        import_block_lines.append(lines[next_line_idx])
                        if (lines[next_line_idx].strip().endswith("\"\"\"") or lines[next_line_idx].strip().endswith("'''")):
                            break
                continue

            if stripped_line.startswith("import ") or stripped_line.startswith("from "):
                import_block_lines.append(line_text)
                if "(" in stripped_line and ")" not in stripped_line:
                    in_multiline_import = True
                continue
            
            # If we reach here, it's the first non-import, non-comment, non-blank, non-docstring line
            break 

        return "\n".join(import_block_lines)

    def _extract_class_method_context(self, file_content: str, class_name: str, method_name: Optional[str]) -> str:
        """
        Extracts the context for a specific class. If method_name is provided and found,
        extracts only that method's definition. Otherwise, extracts the entire class.
        Uses AST parsing. Returns empty string on syntax error or if not found.

        Args:
            file_content: The full content of the Python file as a string.
            class_name: The name of the class to find.
            method_name: The name of the method. If None, extracts the class.
                         If specified and found, extracts only the method.
                         If specified but not found, extracts the class.

        Returns:
            String of the class/method context, or empty string.
        
        Example:
            content = "class A:\\n  def m1(self): pass\\n  def m2(self): pass"
            _extract_class_method_context(content, "A", "m1") # Returns "  def m1(self): pass"
            _extract_class_method_context(content, "A", None) # Returns "class A:\\n  def m1(self): pass\\n  def m2(self): pass"
        """
        try:
            tree = ast.parse(file_content)
            lines = file_content.splitlines()
            for node in ast.walk(tree):
                if isinstance(node, ast.ClassDef) and node.name == class_name:
                    if method_name:
                        for child_node in node.body:
                            if isinstance(child_node, ast.FunctionDef) and child_node.name == method_name:
                                # Extract just the method lines
                                start = child_node.lineno -1
                                end = child_node.end_lineno if hasattr(child_node, 'end_lineno') and child_node.end_lineno is not None else start + (len(ast.unparse(child_node).splitlines()) if hasattr(ast, 'unparse') else 1)
                                return "\n".join(lines[start:end])
                        logger.warning(f"Method '{method_name}' not found in class '{class_name}'. Returning full class context.")
                    # Fallback to returning full class if method_name is None or method not found
                    class_start = node.lineno - 1
                    class_end = node.end_lineno if hasattr(node, 'end_lineno') and node.end_lineno is not None else class_start + (len(ast.unparse(node).splitlines()) if hasattr(ast, 'unparse') else 1)
                    return "\n".join(lines[class_start:class_end])
            logger.warning(f"Class '{class_name}' not found in the file.")
            return ""
        except SyntaxError as e:
            logger.error(f"Syntax error parsing file content for context extraction: {e}")
            return ""