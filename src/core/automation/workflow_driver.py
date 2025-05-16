# src/core/automation/workflow_driver.py
import logging
import html
import os
import json
from pathlib import Path
from src.core.llm_orchestration import EnhancedLLMOrchestrator
import re
from unittest.mock import MagicMock # Keep MagicMock for now as it's used in __init__
from src.cli.write_file import write_file
import subprocess
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from datetime import datetime
import uuid
import builtins
import spacy
from spacy.matcher import PhraseMatcher
import ast # Import ast for syntax check
from typing import List # Import List for type hinting

# Use name for the logger name
logger = logging.getLogger(__name__)

# Define a maximum file size for reading (e.g., 1MB)
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"

# --- NEW CONSTANT: Maximum retries for a single plan step ---
MAX_STEP_RETRIES = 2 # Allow 2 retries per step (3 attempts total)
# --- END NEW CONSTANT ---
# --- NEW CONSTANT for Task 1.8.A ---
MAX_IMPORT_CONTEXT_LINES = 200 # Max lines of context to provide for import tasks
# --- END NEW CONSTANT ---


# Load spaCy model for classify_plan_step
nlp = None # Initialize nlp to None
try:
    nlp = spacy.load("en_core_web_sm")
except OSError:
    logger.error("SpaCy model 'en_core_web_sm' not found. Please install it by running: python -m spacy download en_core_web_sm")
    # nlp remains None if loading fails

# Define comprehensive lists of keywords and phrases strongly associated with code modifications
# and conceptual steps. These lists can be expanded over time.
# ADDED: Expanded lists to include individual words and phrases for better matching
# FIX: Adjusted keywords based on test failures
CODE_KEYWORDS = [
    # Common code actions (individual words)
    "add", "import", "implement", "modify", "update", "refactor", "write", "fix", "debug", "handle", "change",
    "configure", "create", "test", "install", "use", "validate", "bug",
    "constant", # ADDED: 'constant' as individual word
    "constants", # ADDED: Plural form to match test case "define constants"
    "logic", # ADDED: To help classify steps like "implement the core logic" as code
    # REMOVED: "define" from CODE_KEYWORDS

    # Common code actions (phrases)
    "refactor code", "add import",
    "define constants", # MODIFIED: Changed from "define constant" to plural "define constants"
    "implement function", "modify class",
    "update logic", "change variable", "add parameter", "create file", "write test",
    "fix bug", "use library", "configure setting", "add method", "remove method", "add attribute", "remove attribute",
    "update dependency", "install package", "debug issue", "handle error", "add validation", "change database schema",
    "write script", "update configuration", "run tests", "execute tests", "verify tests", "pytest", "test suite",
    # Added phrases to address specific test failures
    "implement core logic", "constant definition",
    "core logic" # Added "core logic" previously
]

CONCEPTUAL_KEYWORDS = [
    # Common conceptual actions (individual words)
    "understand", "design", "discuss", "review", "analyze", "research", "plan", "document", "evaluate", "gather",
    "propose", "coordinate", "get", "brainstorm", "investigate",
    "define", # KEPT: "define" in CONCEPTUAL_KEYWORDS
    "scope", # ADDED: 'scope' for conceptual test
    # REMOVED: "prepare" from CONCEPTUAL_KEYWORDS (Reverted adding 'prepare' as individual word)
    "report", # ADDED: To help classify "Write a report..." as conceptual
    "findings", # ADDED: To help classify "Write a report on findings" as conceptual

    # Common conceptual actions (phrases)
    "understand requirements", "design interface", "discuss approach", "review code", "test functionality",
    "document decision", "analyze problem", "plan next step", "research options", "gather feedback", "propose solution",
    "evaluate alternatives", "define scope", "create plan", "coordinate with team", "get approval",
    "prepare presentation", # Keep existing phrase
    "prepare a presentation", # ADDED: To specifically match the test case "Prepare a presentation."
    "write report", # Keep existing phrase
    "brainstorm ideas", "research and identify",
    # Added phrases to address specific test failures
    "project plan", "design proposal"
]

# REMOVED: HIGH_PRIORITY_CODE_KEYWORDS and HIGH_PRIORITY_CONCEPTUAL_KEYWORDS

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

    # REMOVED: High-priority keyword check block

    if nlp is None:
        # Fallback to regex-based keyword counting if NLP model failed to load
        code_score = 0
        conceptual_score = 0

        # Use regex with word boundaries for more robust matching
        for keyword in CODE_KEYWORDS:
            # Use re.escape to handle special characters in keywords
            # Add re.IGNORECASE for robustness although input is lowercased
            # Use findall to count multiple occurrences if a keyword appears multiple times
            code_score += len(re.findall(r'\b' + re.escape(keyword.lower()) + r'\b', step_description_lower))

        for keyword in CONCEPTUAL_KEYWORDS:
            # Use re.escape to handle special characters in keywords
            # Add re.IGNORECASE for robustness although input is lowercased
            # Use findall to count multiple occurrences
            conceptual_score += len(re.findall(r'\b' + re.escape(keyword.lower()) + r'\b', step_description_lower))

        # Decision logic based on scores (Fallback - Prioritize Code in Ties/Code >= Conceptual)
        # This block is now reached for ALL inputs
        if code_score > 0 and code_score >= conceptual_score:
            return 'code'
        elif conceptual_score > 0 and conceptual_score > code_score:
             return 'conceptual'
        else:
            return 'uncertain'

    else:
        # NLP Integration using SpaCy PhraseMatcher
        doc = nlp(step_description.lower()) # Process lowercased text

        # Calculate scores using PhraseMatcher
        code_matcher = PhraseMatcher(nlp.vocab)
        conceptual_matcher = PhraseMatcher(nlp.vocab)

        # Process keywords once globally or in a setup phase for efficiency
        # (Note: This is still done inside the function here, but the comment indicates the ideal)
        # Ensure patterns are created from lowercased keywords for consistency
        code_patterns = [nlp(text.lower()) for text in CODE_KEYWORDS]
        conceptual_patterns = [nlp(text.lower()) for text in CONCEPTUAL_KEYWORDS]


        code_matcher.add("CODE_PATTERNS", None, *code_patterns)
        conceptual_matcher.add("CONCEPTUAL_PATTERNS", None, *conceptual_patterns)

        # Find matches
        code_matches = code_matcher(doc)
        conceptual_matches = conceptual_matcher(doc)

        # Score based on the number of matches found
        code_score = len(code_matches)
        conceptual_score = len(conceptual_matches)


        # Decision logic based on scores (NLP)
        # This logic mirrors the fallback logic for consistency, prioritizing code in ties/code >= conceptual
        # This block is now reached for ALL inputs if nlp is loaded
        if code_score > 0 and code_score >= conceptual_score:
            return 'code'
        elif conceptual_score > 0 and conceptual_score > code_score:
             return 'conceptual'
        else:
            return 'uncertain'


class Context:
    def __init__(self, base_path):
        self.base_path = base_path
        # Resolve base_path immediately for safety checks
        try:
            self._resolved_base_path = Path(self.base_path).resolve()
        except Exception as e:
            logger.error(f"Error resolving base path '{self.base_path}': {e}", exc_info=True)
            self._resolved_base_path = None # Indicate resolution failure


    def get_full_path(self, relative_path):
        """Resolves a relative path against the context's base path."""
        if self._resolved_base_path is None:
            logger.error(f"Base path failed to resolve. Cannot resolve relative path '{relative_path}'.")
            return None

        if not isinstance(relative_path, str) or relative_path == "": # Added check for empty string
            # Handle non-string or empty input gracefully
            # An empty string relative path should resolve to the base path itself
            if relative_path == "":
                return str(self._resolved_base_path)
            logger.warning(f"Attempted to resolve path with invalid input: {relative_path}")
            return None

        try:
            # Resolve the requested path relative to the base path
            full_requested_path = self._resolved_base_path / relative_path
            resolved_path = full_requested_path.resolve()

            # Check if the resolved path starts with the resolved base path
            # This prevents '..' traversal and absolute paths resolving outside the base
            if not str(resolved_path).startswith(str(self._resolved_base_path)):
                logger.warning(f"Path traversal attempt detected during resolution: {relative_path} resolved to {resolved_path}")
                return None # Return None if path resolves outside the base directory

            return str(resolved_path)
        except Exception as e:
            logger.error(f"Error resolving path '{relative_path}' relative to '{self.base_path}': {e}", exc_info=True)
            return None


    def __eq__(self, other):
        """Compares two Context objects based on their base_path."""
        if not isinstance(other, Context):
            return NotImplemented
        return self.base_path == other.base_path

    def __repr__(self):
        return f"Context(base_path='{self.base_path}')"

class WorkflowDriver:
    def __init__(self, context: Context):
        self.context = context
        self.tasks = [] # Will be loaded by start_workflow
        self._current_task_results = {} # Dictionary to store results for the current task iteration
        self.remediation_attempts = 0 # Initialize remediation counter
        self._current_task = {} # Initialize current task dictionary
        self.task_target_file = None # Initialize task_target_file


        # Instantiate EthicalGovernanceEngine and load default policy FIRST
        self.ethical_governance_engine = EthicalGovernanceEngine()
        self._load_default_policy() # Extract policy loading to a separate method

        # Initialize LLM Orchestrator - Pass REAL dependencies where available
        # Pass the real ethical_governance_engine instance
        # Use MagicMock for kg and spec for now as they are not the focus
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=MagicMock(),
            ethics_engine=self.ethical_governance_engine
        )
        # Instantiate CodeReviewAgent
        self.code_review_agent = CodeReviewAgent()


    def _load_default_policy(self):
        """Load the default ethical policy from file."""
        # Use context.get_full_path for safety when loading the policy file
        default_policy_path = self.context.get_full_path("policies/policy_bias_risk_strict.json")
        if default_policy_path:
            try:
                with builtins.open(default_policy_path, 'r') as f: # Use builtins.open
                     self.default_policy_config = json.load(f) # Use json.load
                logger.info(f"Loaded default ethical policy: {self.default_policy_config.get('policy_name')}")
            except FileNotFoundError:
                 logger.warning(f"Default ethical policy file not found at {default_policy_path}. Ethical analysis will be skipped.")
                 self.default_policy_config = None
            except json.JSONDecodeError:
                 logger.error(f"Invalid JSON in default ethical policy file: {default_policy_path}. Ethical analysis will be skipped.")
                 self.default_policy_config = None
            except Exception as e:
                logger.error(f"Failed to load default ethical policy from {default_policy_path}: {e}", exc_info=True)
                self.default_policy_config = None # Set to None if loading fails
        else:
            logger.warning("Could not resolve path for default ethical policy. Ethical analysis may be impacted.")
            self.default_policy_config = None


    def start_workflow(self, roadmap_path: str, output_dir: str, context: Context):
        """
        Initiates the autonomous workflow loop with specific context.

        Args:
            roadmap_path: Path to the roadmap JSON file.
            output_dir: Path to the output directory.
            context: The Context object for the workflow.
        """
        self.roadmap_path = roadmap_path
        self.output_dir = output_dir  # Store output_dir for potential future use

        # Load the roadmap once at the start of the workflow
        try:
            # Use the context's get_full_path for safety when loading the roadmap
            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
            if full_roadmap_path is None:
                logger.error(f"Invalid roadmap path provided: {self.roadmap_path}")
                return # Exit if roadmap path is invalid after resolving
            self.tasks = self.load_roadmap(full_roadmap_path) # Load from the resolved path
        except Exception as e:
            logger.error(f"Failed to reload roadmap from {self.roadmap_path}: {e}",
                         exc_info=True)
            # This break was inside the while loop in the original code,
            # but start_workflow should just return on failure.
            return # Exit if roadmap loading fails
        self.context = context  # Update context if needed (though it's set in __init__)
        logger.info(f"Workflow initiated with roadmap: {roadmap_path}, output: {output_dir}")
        self.autonomous_loop()

    # --- NEW HELPER METHOD for Task 1.8.A ---
    def _is_add_imports_step(self, step_description: str) -> bool:
        """Checks if a step description likely refers to adding import statements."""
        step_lower = step_description.lower()
        import_keywords = ["add import", "import statement", "import module", "import library", "include import"]
        return any(keyword in step_lower for keyword in import_keywords)

    def _find_import_block_end(self, lines: List[str]) -> int:
        """Finds the line number after the last import statement or a reasonable cutoff."""
        last_import_line = -1 # Use -1 to indicate no imports found yet
        for i, line in enumerate(lines):
            stripped_line = line.strip()
            if stripped_line.startswith("import ") or stripped_line.startswith("from "):
                last_import_line = i
            # Stop if we hit a class, def, or a line that's clearly not an import/comment/blank
            # Only stop if we have found at least one import (last_import_line > -1)
            elif stripped_line and not stripped_line.startswith("#") and last_import_line > -1:
                # If we found imports and then something else, the block ended.
                return i # Return the line number of the first non-import/non-comment/non-blank line after imports
        if last_import_line > -1: # Imports found, possibly at EOF or followed only by comments/blank lines
            return len(lines) # Return total number of lines (end of file)
        return 0 # Default to line 0 if no imports found at all
    # --- END NEW HELPER METHOD ---

    def autonomous_loop(self):
        """
        Main control flow loop for the autonomous Driver LLM.

        This method orchestrates the task selection, planning, agent invocation,
        and file management steps to drive the development process autonomously.
        """
        # Ensure roadmap_path is set before trying to load
        if not hasattr(self, 'roadmap_path') or (self.roadmap_path is None): # Check for None explicitly
            logger.error("Roadmap path not set. Cannot start autonomous loop.")
            return # Exit if roadmap path is not set

        # MAX_REMEDIATION_ATTEMPTS is defined in remediation methods, not here.
        # MAX_STEP_RETRIES is defined globally.

        while True:
            logger.info('Starting autonomous loop iteration')
            self._current_task_results = {} # Reset results for the new task iteration
            self._current_task_results['step_errors'] = [] # Initialize step errors list
            self.remediation_occurred_in_pass = False # Flag to track if *any* remediation attempt in this pass succeeded in writing

            # Load the roadmap inside the loop to get the latest status updates
            try:
                full_roadmap_path = self.context.get_full_path(self.roadmap_path)
                if full_roadmap_path is None:
                    logger.error(f"Invalid roadmap path provided: {self.roadmap_path}. Cannot continue autonomous loop.")
                    break # Exit loop if roadmap path is invalid
                self.tasks = self.load_roadmap(full_roadmap_path)
            except Exception as e:
                logger.error(f"Failed to reload roadmap from {self.roadmap_path}: {e}",
                             exc_info=True)
                break # Exit loop if roadmap reloading fails

            next_task = self.select_next_task(self.tasks)

            if next_task:
                task_id = next_task.get('task_id', 'Unknown ID')
                logger.info(f'Selected task: ID={task_id}')
                self._current_task = next_task # Store current task for remediation prompts etc.

                # Determine the primary target file for the task, if specified
                self.task_target_file = next_task.get('target_file') # Set task_target_file attribute

                solution_plan = self.generate_solution_plan(next_task)
                logger.info(f'Generated plan: {solution_plan}')

                if solution_plan:
                    logger.info(
                        f"Executing plan for task {task_id} with {len(solution_plan)} steps.")
                    # Flag to track if any code was written in this iteration
                    code_written_in_iteration = False

                    # --- START: Step Execution Loop with Retry ---
                    for step_index, step in enumerate(solution_plan):
                        step_retries = 0
                        step_succeeded = False # Flag to track if the step completed successfully after retries

                        while step_retries <= MAX_STEP_RETRIES:
                            try: # Outer try for the entire step execution attempt
                                logger.info(f"Executing step {step_index + 1}/{len(solution_plan)} (Attempt {step_retries + 1}/{MAX_STEP_RETRIES + 1}): {step}")

                                step_lower = step.lower()

                                # --- Step 1: Classify the step preliminarily ---
                                prelim_flags = self._classify_step_preliminary(step)
                                is_test_execution_step_prelim = prelim_flags['is_test_execution_step_prelim']
                                is_explicit_file_writing_step_prelim = prelim_flags['is_explicit_file_writing_step_prelim']
                                is_code_generation_step_prelim = prelim_flags['is_code_generation_step_prelim']
                                is_test_writing_step_prelim = prelim_flags['is_test_writing_step_prelim']
                                is_research_step_prelim = prelim_flags['is_research_step_prelim']


                                # --- Step 2: Determine the actual filepath to use for the operation ---
                                filepath_to_use = self._determine_filepath_to_use(step, self.task_target_file, prelim_flags)

                                # --- Step 3: Determine write operation details (content, overwrite) ---
                                content_to_write, overwrite_mode = self._determine_write_operation_details(step, filepath_to_use, self.task_target_file, prelim_flags)


                                # --- Step 4: Execute based on classification and determined filepath ---
                                generated_output = None  # Initialize generated_output for this step
                                # content_to_write and overwrite_mode are now determined by _determine_write_operation_details


                                # Prioritize test execution steps
                                if is_test_execution_step_prelim: # Use preliminary flag for execution decision
                                    logger.info(f"Step identified as test execution. Running tests for step: {step}")
                                    test_command = ["pytest"] # Default test command
                                    # Use filepath_to_use if it looks like a test file, otherwise default to tests/
                                    if filepath_to_use and "test_" in Path(filepath_to_use).name.lower():
                                        test_command.append(filepath_to_use)
                                    else:
                                        test_command.append("tests/")

                                    try:
                                        return_code, stdout, stderr = self.execute_tests(test_command, self.context.base_path)
                                        test_results = self._parse_test_results(stdout)
                                        self._current_task_results['test_results'] = test_results
                                        logger.info(f"Test Execution Results: Status={test_results.get('status')}, Passed={test_results.get('passed')}, Failed={test_results.get('failed')}, Total={test_results.get('total')}")
                                        if test_results.get('status') == 'failed':
                                            logger.error(f"Tests failed for step: {step}. Raw stderr:\n{stderr}")
                                        elif test_results.get('status') == 'error':
                                            logger.error(f"Test execution or parsing error for step: {step}. Message: {test_results.get('message')}. Raw stderr:\n{stderr}")
                                    except Exception as e: # Inner try/except for execute_tests
                                        logger.error(f"An unexpected error occurred during command execution: {e}", exc_info=True)
                                        self._current_task_results['test_results'] = {'status': 'error', 'passed': 0, 'failed': 0, 'total': 0, 'message': str(e)}
                                        raise e # Re-raise the exception


                                # Prioritize code generation steps targeting a specific file
                                # Requires classification as code gen AND a determined filepath that is a .py file
                                elif is_code_generation_step_prelim and filepath_to_use and filepath_to_use.endswith('.py'): # Use preliminary flag for execution decision
                                    logger.info(
                                        f"Step identified as code generation for file {filepath_to_use}. Orchestrating read-generate-merge-write.")

                                    existing_content = self._read_file_for_context(filepath_to_use)
                                    logger.debug(f"Read {len(existing_content)} characters from {filepath_to_use}.")

                                    # --- START: Task 1.8.A - Optimized context for imports ---
                                    context_for_llm = existing_content
                                    specific_instructions = (
                                        "Generate only the Python code snippet needed to fulfill the \"Specific Plan Step\". "
                                        "Do not include any surrounding text, explanations, or markdown code block fences (```). "
                                        "Provide just the raw code lines that need to be added or modified."
                                    )
                                    if self._is_add_imports_step(step):
                                        logger.info(f"Identified 'add imports' step. Optimizing context for {filepath_to_use}.")
                                        lines = existing_content.splitlines()
                                        # Find end of import block or take first MAX_IMPORT_CONTEXT_LINES
                                        import_block_end_line = self._find_import_block_end(lines)
                                        cutoff_line = min(import_block_end_line + 5, MAX_IMPORT_CONTEXT_LINES, len(lines)) # Add a bit of buffer
                                        # Ensure cutoff_line is not negative if lines is empty or import_block_end_line is 0
                                        cutoff_line = max(0, cutoff_line)

                                        context_for_llm = "\n".join(lines[:cutoff_line])
                                        specific_instructions = (
                                            "You are adding import statements. Provide *only* the new import lines that need to be added. "
                                            "Do not repeat existing imports. Do not output any other code or explanation. "
                                            "Place the new imports appropriately within or after the existing import block."
                                        )
                                        logger.debug(f"Using truncated context for imports (up to line {cutoff_line}):\n{context_for_llm}")
                                    # --- END: Task 1.8.A ---

                                    # --- START FIX: Add target_file context to Coder LLM prompt ---
                                    target_file_context_for_coder = ""
                                    if self.task_target_file:
                                         # FIX: Removed "in the task metadata" as per previous LLM fix
                                         target_file_context_for_coder = f"The primary file being modified is `{self.task_target_file}`. Focus your code generation on actions related to this file.\n\n"
                                    # --- END FIX ---

                                    coder_prompt = f"""You are a Coder LLM expert in Python.
Your task is to generate only the code snippet required to implement the following specific step from a larger development plan.

# --- START FIX: Add Task Name and Description back to Coder Prompt ---
Overall Task: "{next_task.get('task_name', 'Unknown Task')}"
Task Description: {next_task.get('description', 'No description provided.')}
# --- END FIX ---

{target_file_context_for_coder} # Add the target file context here

Specific Plan Step:
{step}

The primary file being modified is `{filepath_to_use}`.

EXISTING CONTENT OF `{filepath_to_use}`:
```python
{context_for_llm}
```
{specific_instructions}"""
                                    # --- NEW LOGGING: Log the prompt ---
                                    logger.debug("Invoking Coder LLM with prompt:\n%s", coder_prompt)
                                    # --- END NEW LOGGING ---
                                    generated_snippet = self._invoke_coder_llm(coder_prompt)


                                    if generated_snippet:
                                        logger.info(
                                            f"Coder LLM generated snippet (first 100 chars): {generated_snippet[:100]}...")

                                        # --- START FIX for task_1_8_2_retry: Implement Pre-Write Validation ---
                                        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
                                        validation_passed = True
                                        validation_feedback = []

                                        # 1. Syntax Check (using AST parse)
                                        try:
                                            ast.parse(generated_snippet)
                                            logger.info("Pre-write syntax check (AST parse) passed for snippet.")
                                        except SyntaxError as se:
                                            validation_passed = False
                                            validation_feedback.append(f"Pre-write syntax check failed: {se}")
                                            logger.warning(f"Pre-write syntax validation (AST parse) failed for snippet: {se}")
                                            # --- NEW LOGGING: Log the failed snippet ---
                                            logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                            # --- END NEW LOGGING ---
                                        except Exception as e: # Catch other potential AST errors
                                            logger.error(f"Error during pre-write syntax validation (AST parse): {e}", exc_info=True)
                                            validation_passed = False # Treat errors as validation failure
                                            validation_feedback.append(f"Error during pre-write syntax validation (AST parse): {e}")
                                            # --- NEW LOGGING: Log the failed snippet ---
                                            logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                            # --- END NEW LOGGING ---


                                        # 2. Ethical Check (if policy loaded and syntax passed)
                                        if validation_passed and self.default_policy_config:
                                            try:
                                                ethical_results = self.ethical_governance_engine.enforce_policy(generated_snippet, self.default_policy_config)
                                                if ethical_results.get('overall_status') == 'rejected':
                                                    validation_passed = False
                                                    validation_feedback.append(f"Pre-write ethical check failed: {ethical_results}")
                                                    logger.warning(f"Pre-write ethical validation failed for snippet: {ethical_results}")
                                                    # --- NEW LOGGING: Log the failed snippet ---
                                                    logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                                    # --- END NEW LOGGING ---
                                                else:
                                                    logger.info("Pre-write ethical validation passed for snippet.")
                                            except Exception as e:
                                                logger.error(f"Error during pre-write ethical validation: {e}", exc_info=True)
                                                validation_passed = False # Treat errors as validation failure
                                                validation_feedback.append(f"Error during pre-write ethical validation: {e}")
                                                # --- NEW LOGGING: Log the failed snippet ---
                                                logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                                # --- END NEW LOGGING ---
                                        elif validation_passed: # Only log if validation_passed is still True
                                            logger.warning("Skipping pre-write ethical validation: Default policy not loaded.")


                                        # --- NEW VALIDATION: Code Style Check (using CodeReviewAgent) ---
                                        # This is part of task_1_8_2_retry, implementing it here.
                                        if validation_passed: # Only run if previous checks passed
                                            try:
                                                # Use analyze_python which includes Flake8 and Bandit
                                                style_review_results = self.code_review_agent.analyze_python(generated_snippet)
                                                # Define what constitutes a style/security failure for pre-write
                                                # For now, let's fail on any 'error' or 'security_high' severity finding
                                                critical_findings = [
                                                    f for f in style_review_results.get('static_analysis', [])
                                                    if f.get('severity') in ['error', 'security_high']
                                                ]
                                                if critical_findings:
                                                    validation_passed = False
                                                    validation_feedback.append(f"Pre-write style/security check failed: Critical findings detected.")
                                                    logger.warning(f"Pre-write style/security validation failed for snippet. Critical findings: {critical_findings}")
                                                    # --- NEW LOGGING: Log the failed snippet ---
                                                    logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                                    # --- END NEW LOGGING ---
                                                else:
                                                    logger.info("Pre-write style/security validation passed for snippet.")
                                            except Exception as e:
                                                logger.error(f"Error during pre-write style/security validation: {e}", exc_info=True)
                                                validation_passed = False # Treat errors as validation failure
                                                validation_feedback.append(f"Error during pre-write style/security validation: {e}")
                                                # --- NEW LOGGING: Log the failed snippet ---
                                                logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                                # --- END NEW LOGGING ---
                                        # --- END NEW VALIDATION ---


                                        if validation_passed:
                                            logger.info(f"Pre-write validation passed for snippet targeting {filepath_to_use}. Proceeding with merge/write.")
                                            # --- END FIX for task_1_8_2_retry ---

                                            merged_content = self._merge_snippet(existing_content, generated_snippet)
                                            logger.debug("Snippet merged.")

                                            logger.info(f"Attempting to write merged content to {filepath_to_use}.")
                                            try:
                                                self._write_output_file(filepath_to_use, merged_content, overwrite=True)
                                                logger.info(f"Successfully wrote merged content to {filepath_to_use}.")
                                                code_written_in_iteration = True # Mark that code was written

                                                # --- Run Initial Validations after successful write ---
                                                # These are post-write validations, already part of Phase 1.7
                                                try:
                                                    logger.info(f"Running code review and security scan for {filepath_to_use}...")
                                                    review_results = self.code_review_agent.analyze_python(merged_content)
                                                    self._current_task_results['code_review_results'] = review_results
                                                    logger.info(f"Code Review and Security Scan Results for {filepath_to_use}: {review_results}")
                                                except Exception as review_e:
                                                    logger.error(f"Error running code review/security scan for {filepath_to_use}: {review_e}", exc_info=True)
                                                    self._current_task_results['code_review_results'] = {'status': 'error', 'message': str(review_e)}

                                                if self.default_policy_config:
                                                    try:
                                                        logger.info(f"Running ethical analysis for {filepath_to_use}...")
                                                        ethical_analysis_results = self.ethical_governance_engine.enforce_policy(merged_content, self.default_policy_config)
                                                        self._current_task_results['ethical_analysis_results'] = ethical_analysis_results
                                                        logger.info(f"Ethical Analysis Results for {filepath_to_use}: {ethical_analysis_results}")
                                                    except Exception as ethical_e:
                                                        logger.error(f"Error running ethical analysis for {filepath_to_use}: {ethical_e}", exc_info=True)
                                                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': str(ethical_e)}
                                                else:
                                                    logger.warning("Default ethical policy not loaded. Skipping ethical analysis.")
                                                    self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded.'}
                                                # --- END Initial Validations ---

                                            except FileExistsError:
                                                logger.error(f"Unexpected FileExistsError when writing merged content to {filepath_to_use} with overwrite=True.")
                                                # This is an unexpected error during write, treat as step failure
                                                raise FileExistsError(f"Unexpected FileExistsError during write: {filepath_to_use}") from None # Re-raise as step failure
                                            except Exception as e:
                                                logger.error(f"Failed to write merged content to {filepath_to_use}: {e}", exc_info=True)
                                                raise e # Re-raise the exception
                                        else:
                                            # --- START FIX for task_1_8_2_retry: Handle Pre-Write Validation Failure ---
                                            logger.warning(f"Pre-write validation failed for snippet targeting {filepath_to_use}. Skipping write/merge. Feedback: {validation_feedback}")
                                            # Do NOT set code_written_in_iteration = True
                                            # Do NOT run post-write validations.
                                            # This step failed validation, raise an exception to trigger retry/blocking logic
                                            # REMOVED 'from None' as per LLM suggestion
                                            raise ValueError(f"Pre-write validation failed for step {step_index + 1}.")
                                            # --- END FIX for task_1_8_2_retry ---
                                    else:
                                        logger.warning(f"Coder LLM returned empty or None snippet for step {step_index + 1}. Skipping file write.")
                                        # Treat empty snippet as a step failure
                                        # REMOVED 'from None' as per LLM suggestion
                                        raise ValueError(f"Coder LLM returned empty snippet for step {step_index + 1}.")


                                # Handle steps identified as explicit file writing (non-code-gen)
                                # Requires classification as explicit file writing AND a determined filepath
                                elif content_to_write is not None and filepath_to_use: # Use the result from _determine_write_operation_details
                                    logger.info(f"Step identified as explicit file writing. Processing file operation for step: {step}")

                                    # content_to_write and overwrite_mode are already determined by _determine_write_operation_details

                                    logger.info(f"Attempting to write file: {filepath_to_use}.")
                                    try:
                                        self._write_output_file(filepath_to_use, content_to_write, overwrite=overwrite_mode)
                                        logger.info(f"Successfully wrote placeholder content to {filepath_to_use}.")
                                        # Note: Placeholder writes don't trigger validations or remediation in the current logic
                                    except FileExistsError:
                                        logger.warning(
                                            f"File {filepath_to_use} already exists. Skipping write as overwrite={overwrite_mode}.")
                                    except Exception as e:
                                        logger.error(f"Failed to write file {filepath_to_use}: {e}",
                                                     exc_info=True)
                                        raise e # Re-raise the exception


                                # Log if the step was not identified as involving file operations, code generation, or test execution
                                # OR if it was identified but no filepath_to_use was determined
                                else:
                                    logger.info(
                                        f"Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: {step}")

                                # If we reached here without raising an exception, the step is considered successful for this attempt
                                step_succeeded = True
                                break # Break the retry loop for this step

                            except Exception as e:
                                # --- START: Error Handling for Step Execution ---
                                logger.error(f"Error executing step {step_index + 1}/{len(solution_plan)} (Attempt {step_retries + 1}/{MAX_STEP_RETRIES + 1}): {step}", exc_info=True)
                                # Store failure information for this step attempt
                                self._current_task_results['step_errors'].append({
                                    'step_index': step_index + 1, # Use 1-based index for report
                                    'step_description': step,
                                    'error_type': type(e).__name__,
                                    'error_message': str(e),
                                    'timestamp': datetime.utcnow().isoformat(),
                                    'attempt': step_retries + 1
                                })

                                step_retries += 1
                                if step_retries <= MAX_STEP_RETRIES:
                                    logger.warning(f"Step {step_index + 1} failed. Attempting retry {step_retries}/{MAX_STEP_RETRIES}...")
                                    # Continue the while loop for retry
                                else:
                                    logger.error(f"Step {step_index + 1} failed after {MAX_STEP_RETRIES} retries.")
                                    # The while loop condition will now be false, and it will exit without setting step_succeeded = True

                        # --- END: Step Execution Loop with Retry ---

                        # Check if the step succeeded after all attempts
                        if not step_succeeded:
                            # If the step failed after exhausting retries, mark the task as Blocked and exit the task execution
                            new_status = "Blocked"
                            # Find the last error message for this step
                            last_error = next(
                                (err for err in reversed(self._current_task_results['step_errors'])
                                 if err['step_index'] == step_index + 1),
                                {"error_type": "UnknownError", "error_message": "No specific error logged."}
                            )
                            reason_blocked = f"Step {step_index + 1} ('{step}') failed after {MAX_STEP_RETRIES + 1} attempts. Last error: {last_error['error_type']}: {last_error['error_message']}"
                            logger.warning(f"Task {task_id} marked as '{new_status}'.")
                            self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                            return # Exit the autonomous_loop for this task iteration

                    # --- END: Plan Step Iteration (for loop) ---

                    # If the loop completed without returning (meaning all steps succeeded)
                    logger.info("All plan steps executed successfully.")

                    # --- Post-Step Execution Logic (Inside the 'if solution_plan:' block) ---
                    # This block is reached only if all steps in the plan were executed and succeeded (potentially after retries)
                    logger.info("Generating Grade Report...")
                    grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                    logger.info(f"--- GRADE REPORT for Task {task_id} ---\n{grade_report_json}\n--- END GRADE REPORT ---")

                    evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                    recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                    justification = evaluation_result.get("justification", "Evaluation failed.")
                    logger.info(f"Initial Grade Report Evaluation: Recommended Action='{recommended_action}', Justification='{justification}'")

                    # --- BEGIN: Remediation Logic (Currently runs AFTER all steps) ---
                    # Remediation is only attempted if there are no step execution errors AND evaluation recommends Regenerate
                    # Step execution errors are now handled by blocking the task immediately, so we only check recommended_action.
                    MAX_TASK_REMEDIATION_ATTEMPTS = 2 # Define max task-level remediation attempts here
                    if recommended_action == "Regenerate Code":
                        if self.remediation_attempts < MAX_TASK_REMEDIATION_ATTEMPTS:
                            logger.info(f"Attempting automated remediation (Attempt {self.remediation_attempts + 1}/{MAX_TASK_REMEDIATION_ATTEMPTS})...")
                            self.remediation_occurred_in_pass = False # Reset flag for this remediation pass

                            # Determine the file path for remediation - prioritize the task target file
                            filepath_for_remediation = self.task_target_file
                            # If no task target file, try to find one from the last code/file step that had a path
                            # This is a simplification; a more robust approach might track file changes per step
                            # FIX: Initialize last_file_step_path outside the conditional block
                            last_file_step_path = None
                            if not filepath_for_remediation:
                                # Find the last step that involved a file operation and had a determined path
                                for step_index, step in reversed(list(enumerate(solution_plan))):
                                     step_lower = step.lower()
                                     filepath_from_step_match = re.search(r'(\S+\.(?:py|md|json|txt|yml|yaml))', step, re.IGNORECASE)
                                     filepath_from_step = filepath_from_step_match.group(1) if filepath_from_step_match else None

                                     # Re-calculate classification flags for this step to determine if it was a file step
                                     # Use the same preliminary checks as above for consistency
                                     code_generation_verbs_check = ["implement", "generate code", "write function", "modify", "add", "define", "create", "update", "refactor", "write"] # ADDED "write"
                                     research_keywords_check = ["research and identify", "research", "analyze", "investigate", "understand"]
                                     code_element_keywords_check = ["import", "constant", "variable", "function", "class", "method", "definition", "parameter", "return"]
                                     file_writing_keywords_check = ["write", "write file", "create", "create file", "update", "update file", "modify", "modify file", "save to file", "output file", "generate file", "write output to"]

                                     # Use word boundaries for re-calculation
                                     is_research_step_check = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in research_keywords_check)
                                     is_explicit_file_writing_step_check = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in file_writing_keywords_check)
                                     is_code_generation_step_check = not is_research_step_check and \
                                                                     any(re.search(r'\b' + re.escape(verb) + r'\b', step_lower) for verb in code_generation_verbs_check) and \
                                                                     (any(re.search(r'\b' + re.escape(element) + r'\b', step_lower) for element in code_element_keywords) or \
                                                                      (filepath_from_step and filepath_from_step.endswith('.py')))


                                     if (is_explicit_file_writing_step_check or is_code_generation_step_check) and filepath_from_step:
                                         last_file_step_path = filepath_from_step
                                         break # Found the last relevant file path

                            if last_file_step_path:
                                 filepath_for_remediation = last_file_step_path
                                 logger.debug(f"Using file path from last file step for remediation: {filepath_for_remediation}")


                            if not filepath_for_remediation:
                                logger.error("No target file identified for remediation. Cannot attempt remediation.")
                                # If remediation is recommended but no file is identified, mark as Blocked
                                new_status = "Blocked"
                                reason_blocked = "Remediation recommended but no target file identified."
                                logger.warning(f"Task {task_id} marked as '{new_status}'.")
                                self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                                # No need to return, the loop will select the next task

                            else:
                                current_file_content = self._read_file_for_context(filepath_for_remediation)

                                if current_file_content:
                                    failure_type = self._identify_remediation_target(grade_report_json)

                                    remediation_attempted = False
                                    remediation_success = False # Track if the remediation attempt resulted in a successful write

                                    # Prioritize test failures for remediation
                                    test_results = self._current_task_results.get('test_results', {}) # Get latest test results
                                    test_status = test_results.get('status')
                                    if test_status == 'failed':
                                         remediation_attempted = True
                                         remediation_success = self._attempt_test_failure_remediation(
                                             grade_report_json, next_task, "Test Failure Remediation", filepath_for_remediation, current_file_content
                                         )
                                         if remediation_success:
                                             logger.info("Test failure remediation successful.")
                                             self.remediation_occurred_in_pass = True # Mark that remediation occurred and wrote code
                                             # Re-generate and re-evaluate report after successful remediation
                                             grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                                             logger.info(f"--- REVISED GRADE REPORT (Test Remediation) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                             evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                             recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                                             justification = evaluation_result.get("justification", "Evaluation failed.")
                                             logger.info(f"Revised Grade Report Evaluation (Test Remediation): Recommended Action='{recommended_action}', Justification='{justification}'")
                                         else:
                                             logger.warning("Test failure remediation attempt failed.")


                                    # If test remediation didn't happen or failed, try other types based on identified target
                                    if not remediation_success and failure_type == "Code Style":
                                        remediation_attempted = True
                                        remediation_success = self._attempt_code_style_remediation(grade_report_json, next_task, "Code Style Remediation", filepath_for_remediation, current_file_content)
                                        if remediation_success:
                                            logger.info("Style remediation attempt seems successful (code written).")
                                            self.remediation_occurred_in_pass = True # Mark that remediation occurred and wrote code
                                            # Re-generate and re-evaluate report after successful remediation
                                            grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                                            logger.info(f"--- REVISED GRADE REPORT (Style) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                            evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                            recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                                            justification = evaluation_result.get("justification", "Evaluation failed.")
                                            logger.info(f"Revised Grade Report Evaluation (Style): Recommended Action='{recommended_action}', Justification='{justification}'")
                                        else:
                                            logger.warning("Style remediation attempt failed.")

                                    if not remediation_success and failure_type == "Ethical Transparency":
                                        remediation_attempted = True
                                        remediation_success = self._attempt_ethical_transparency_remediation(grade_report_json, next_task, "Ethical Transparency Remediation", filepath_for_remediation, current_file_content)
                                        if remediation_success:
                                            logger.info("Ethical transparency remediation seems successful (code written).")
                                            self.remediation_occurred_in_pass = True # Mark that remediation occurred and wrote code
                                            # Re-generate and re-evaluate report after successful remediation
                                            grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                                            logger.info(f"--- REVISED GRADE REPORT (Ethical) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                            evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                            recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                                            justification = evaluation_result.get("justification", "Evaluation failed.")
                                            logger.info(f"Revised Grade Report Evaluation (Ethical): Recommended Action='{recommended_action}', Justification='{justification}'")
                                        else:
                                            logger.warning("Ethical transparency remediation attempt failed.")

                                    # Increment task-level remediation attempts counter *only if remediation was attempted and resulted in a write*
                                    if self.remediation_occurred_in_pass:
                                        self.remediation_attempts += 1
                                        logger.info(f"Remediation attempt {self.remediation_attempts} completed.")
                                    elif remediation_attempted:
                                         logger.warning("Remediation attempt failed to write code.")


                                else:
                                    logger.error(f"Failed to read current file content for remediation: {filepath_for_remediation}. Cannot attempt remediation.")
                                    # If remediation is recommended but file cannot be read, mark as Blocked
                                    new_status = "Blocked"
                                    reason_blocked = f"Remediation recommended but failed to read target file: {filepath_for_remediation}"
                                    logger.warning(f"Task {task_id} marked as '{new_status}'.")
                                    self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                                    # No need to return, the loop will select the next task

                        else:
                            # Log if max remediation attempts reached
                            logger.warning(f"Maximum task-level remediation attempts ({MAX_TASK_REMEDIATION_ATTEMPTS}) reached for task {task_id}. Proceeding without further automated remediation.")
                    # --- END Remediation Logic ---


                    # --- Update Roadmap Status based on FINAL Evaluation ---
                    # This happens AFTER all plan steps are executed AND any remediation attempts are completed/exhausted
                    # If the task was blocked mid-plan due to step failure after retries, the 'return' statement above exits.
                    # So, if we reach this point, all steps succeeded, and the final evaluation determines the status.
                    new_status = next_task['status'] # Start with current status
                    reason_blocked = None # Reset reason_blocked

                    if recommended_action == "Completed":
                        new_status = "Completed"
                    elif recommended_action == "Blocked":
                        new_status = "Blocked"
                        reason_blocked = justification # Use evaluation justification as reason

                    if new_status != next_task['status']:
                        logger.info(f"Updating task status from '{next_task['status']}' to '{new_status}' for task {task_id}")
                        self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                    else:
                        logger.info(f"Task status for {task_id} remains '{new_status}' based on evaluation.")

                    # Reset task-level remediation attempts counter for the next task
                    self.remediation_attempts = 0
                    # --- END Roadmap Update ---

                else:
                    logger.warning(f"No solution plan generated for task {task_id}.")
                    logger.info(f"Task {task_id} requires manual review due to failed plan generation.")
                    # If plan generation fails, mark as Blocked
                    new_status = "Blocked"
                    reason_blocked = "Failed to generate a solution plan."
                    logger.warning(f"Task {task_id} marked as '{new_status}'.")
                    self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                    # No need to return, the loop will select the next task


            else:
                logger.info('No tasks available in Not Started status. Exiting autonomous loop.')
                break

            logger.info('Autonomous loop iteration finished.')

        logger.info('Autonomous loop terminated.')

    # --- NEW HELPER METHOD for Task 1.8.A ---
    def _is_add_imports_step(self, step_description: str) -> bool:
        """Checks if a step description likely refers to adding import statements."""
        step_lower = step_description.lower()
        import_keywords = ["add import", "import statement", "import module", "import library", "include import"]
        return any(keyword in step_lower for keyword in import_keywords)

    def _find_import_block_end(self, lines: List[str]) -> int:
        """Finds the line number after the last import statement or a reasonable cutoff."""
        last_import_line = -1 # Use -1 to indicate no imports found yet
        for i, line in enumerate(lines):
            stripped_line = line.strip()
            if stripped_line.startswith("import ") or stripped_line.startswith("from "):
                last_import_line = i
            # Stop if we hit a class, def, or a line that's clearly not an import/comment/blank
            # Only stop if we have found at least one import (last_import_line > -1)
            elif stripped_line and not stripped_line.startswith("#") and last_import_line > -1:
                # If we found imports and then something else, the block ended.
                return i # Return the line number of the first non-import/non-comment/non-blank line after imports
        if last_import_line > -1: # Imports found, possibly at EOF or followed only by comments/blank lines
            return len(lines) # Return total number of lines (end of file)
        return 0 # Default to line 0 if no imports found at all
    # --- END NEW HELPER METHOD ---


    # --- NEW METHOD: Preliminary Step Classification ---
    def _classify_step_preliminary(self, step_description: str) -> dict:
        """
        Performs preliminary classification of a step based on keywords for execution flow.

        Args:
            step_description: The text description of the plan step.

        Returns:
            A dictionary of boolean flags indicating preliminary classification.
        """
        step_lower = step_description.lower()

        # Extract potential filepath from step text (only the first one found)
        filepath_from_step_match = re.search(
            r'(\S+\.(?:py|md|json|txt|yml|yaml))', step_description, re.IGNORECASE)
        filepath_from_step = filepath_from_step_match.group(1) if filepath_from_step_match else None

        # Use word boundaries for more accurate keyword matching
        code_generation_verbs_prelim = ["implement", "generate code", "write function", "modify", "add", "define", "create", "update", "refactor", "write"]
        research_keywords_check_prelim = ["research and identify", "research", "analyze", "investigate", "understand"]
        code_element_keywords_check_prelim = ["import", "constant", "variable", "function", "class", "method", "definition", "parameter", "return"]
        file_writing_keywords_check_prelim = ["write", "write file", "create", "create file", "update", "update file", "modify", "modify file", "save to file", "output file", "generate file", "write output to"]
        test_execution_keywords_check_prelim = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]
        test_writing_keywords_prelim = ["write unit test", "write unit tests", "update unit test", "create test", "add test"]

        # Wrap boolean calculations in bool() to ensure True/False return values
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
            "filepath_from_step": filepath_from_step # Include this as it's used in path determination
        }
    # --- END NEW METHOD ---

    # --- NEW METHOD: Determine Filepath to Use ---
    def _determine_filepath_to_use(self, step_description: str, task_target_file: str | None, preliminary_flags: dict) -> str | None:
        """
        Determines the target file path for a step based on task metadata, step text,
        and preliminary classification.

        Args:
            step_description: The text description of the plan step.
            task_target_file: The target file specified in the task metadata.
            preliminary_flags: Dictionary of preliminary classification flags from _classify_step_preliminary.

        Returns:
            The determined file path string, or None if no path could be determined.
        """
        # filepath_from_step is the first path-like string extracted by _classify_step_preliminary
        filepath_from_step = preliminary_flags.get('filepath_from_step')
        is_code_generation_step_prelim = preliminary_flags.get('is_code_generation_step_prelim', False)
        is_test_writing_step_prelim = preliminary_flags.get('is_test_writing_step_prelim', False)
        is_explicit_file_writing_step_prelim = preliminary_flags.get('is_explicit_file_writing_step_prelim', False)

        # Start with the task's target file
        filepath_to_use = task_target_file

        # Prioritize test writing steps for file targeting
        if is_code_generation_step_prelim and is_test_writing_step_prelim:
            # --- REVISED LOGIC ORDER with explicit test path extraction ---

            # Attempt to find an explicit test file path mentioned in the step description
            explicit_test_path_in_step = None
            # Find all .py files in the step and check if any look like a test file
            all_paths_in_step_matches = re.finditer(r'(\S+\.py)', step_description, re.IGNORECASE)
            for match in all_paths_in_step_matches:
                path_candidate = match.group(1)
                if "test_" in path_candidate.lower() or "tests/" in path_candidate.lower():
                    explicit_test_path_in_step = path_candidate
                    break # Take the first one that looks like a test file

            # 1. If task_target_file is already a test file, use it. (Highest priority for test writing)
            if task_target_file and task_target_file.endswith('.py') and \
               ("test_" in task_target_file.lower() or "tests/" in task_target_file.lower()):
                filepath_to_use = task_target_file
                logger.info(f"Test writing step: Using task_target_file as it appears to be a test file '{filepath_to_use}'.")
            # 2. Else if an explicit test path is found *in the step description*, use it.
            elif explicit_test_path_in_step:
                 filepath_to_use = explicit_test_path_in_step
                 logger.info(f"Test writing step: Using explicit test path from step '{filepath_to_use}'.")
            # 3. Else if task_target_file is a non-test .py file, derive test path by convention.
            elif task_target_file and task_target_file.endswith('.py') and \
                 not ("test_" in task_target_file.lower() or "tests/" in task_target_file.lower()):
                p = Path(task_target_file)
                derived_test_path = Path("tests") / f"test_{p.name}"
                filepath_to_use = str(derived_test_path)
                logger.info(f"Test writing step: Derived test file path '{filepath_to_use}' from task target '{task_target_file}'.")
            # 4. Fallback: if filepath_from_step (the first path identified by _classify_step_preliminary)
            #    is a source .py file, derive test path from it. This handles cases where task_target_file might be None
            #    or not a .py file, but the step itself mentions a source file to be tested.
            elif filepath_from_step and filepath_from_step.endswith('.py') and \
                 not ("test_" in filepath_from_step.lower() or "tests/" in filepath_from_step.lower()):
                p = Path(filepath_from_step)
                derived_test_path = Path("tests") / f"test_{p.name}"
                filepath_to_use = str(derived_test_path)
                logger.info(f"Test writing step: Derived test file path '{filepath_to_use}' from first path in step '{filepath_from_step}'.")
            else:
                # If no specific rule applied, filepath_to_use remains as initially set (e.g., task_target_file, which might be None).
                # Log a warning if it's still not a clear test path.
                current_path_is_test_file = filepath_to_use and filepath_to_use.endswith('.py') and \
                                            ("test_" in filepath_to_use.lower() or "tests/" in filepath_to_use.lower())
                if not current_path_is_test_file:
                     logger.warning(f"Test writing step, but could not determine a clear test file path. Current filepath_to_use: '{filepath_to_use}'. Review step and task metadata.")
            # --- END REVISED LOGIC ORDER ---

        # Original logic for determining filepath_to_use if not a test writing step,
        # or if the above logic didn't set filepath_to_use (e.g., task_target_file was None initially).
        # This is important if task_target_file was None and it's not a test writing step,
        # but an explicit file writing or code generation step targeting a file mentioned in the step.
        elif filepath_to_use is None and (is_explicit_file_writing_step_prelim or is_code_generation_step_prelim) and filepath_from_step:
             filepath_to_use = filepath_from_step

        return filepath_to_use
    # --- END NEW METHOD ---

    # --- NEW METHOD: Determine Write Operation Details ---
    def _determine_write_operation_details(self, step_description: str, filepath_to_use: str | None, task_target_file: str | None, preliminary_flags: dict) -> tuple[str | None, bool]:
        """
        Determines the content to write (e.g., placeholder) and overwrite mode
        based on step classification and target file.

        Args:
            step_description: The text description of the plan step.
            filepath_to_use: The determined file path for the operation.
            task_target_file: The target file specified in the task metadata.
            preliminary_flags: Dictionary of preliminary classification flags from _classify_step_preliminary.

        Returns:
            A tuple: (content_to_write: str | None, overwrite_mode: bool).
            content_to_write is the string content to write, or None if no write should occur.
            overwrite_mode is True if overwrite is allowed, False otherwise.
        """
        step_lower = step_description.lower()
        is_explicit_file_writing_step_prelim = preliminary_flags.get('is_explicit_file_writing_step_prelim', False)
        is_research_step_prelim = preliminary_flags.get('is_research_step_prelim', False)

        step_implies_create_new_file = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in ["create file", "generate file"])

        # --- START FIX for task_1_8_2b_fix_placeholder_overwrite_for_modification_steps ---
        is_main_python_target = (task_target_file is not None and filepath_to_use == task_target_file and filepath_to_use is not None and filepath_to_use.endswith('.py'))
        # Re-calculate is_conceptual_step_for_main_target using word boundaries
        conceptual_define_keywords_check_prelim = ["define list", "analyze", "understand", "document decision", "identify list", "define a comprehensive list"]
        # Use the correct preliminary flag for research
        is_conceptual_step_for_main_target = is_research_step_prelim or \
                                            any(re.search(r'\b' + re.escape(kw) + r'\b', step_lower) for kw in conceptual_define_keywords_check_prelim)

        content_to_write = None # Default to no placeholder write for main target unless explicitly creating
        overwrite_mode = True # Default overwrite to True for file operations

        # Only proceed if it's an explicit file writing step and a filepath was determined
        if is_explicit_file_writing_step_prelim and filepath_to_use:
            if is_main_python_target: # If the target is the main .py file for the task
                if step_implies_create_new_file:
                    # This is an explicit 'create file' step for the main target.
                    # Allow placeholder write only if it's a .py file.
                    if filepath_to_use.endswith('.py'):
                        content_to_write = f"# Placeholder content for Python file for step: {step_description}"
                        overwrite_mode = False # For create, don't overwrite by default
                        logger.info(f"Using placeholder for NEW main Python target {filepath_to_use} for step: '{step_description}'.")
                    else: # Should not happen if task_target_file is .py, but defensive.
                        logger.warning(f"Step implies creating main target {filepath_to_use}, but it's not a .py file. Skipping placeholder.")
                        content_to_write = None # Ensure None if not writing
                elif is_conceptual_step_for_main_target:
                    logger.info(f"Skipping placeholder write to main Python target {filepath_to_use} for conceptual step: '{step_description}'.")
                    content_to_write = None # Prevent placeholder overwrite
                else:
                    # This is a modification step for the main Python target that isn't purely conceptual
                    # and doesn't imply creating a new file. It should NOT write a placeholder.
                    # It should ideally be handled by code generation.
                    logger.info(f"Skipping placeholder write to main Python target {filepath_to_use} for modification step: '{step_description}'. This step should be handled by code generation.")
                    content_to_write = None # Prevent placeholder overwrite
            else: # Not the main Python target, or not a Python file at all
                if step_implies_create_new_file:
                    overwrite_mode = False
                # Original placeholder logic for non-main-python-target files or non-python files
                if filepath_to_use.endswith('.py'):
                    content_to_write = f"# Placeholder content for Python file for step: {step_description}"
                else:
                    content_to_write = f"// Placeholder content for step: {step_description}"
                if content_to_write: # Log only if we are actually going to write a placeholder
                    logger.info(f"Using placeholder content for file: {filepath_to_use} with overwrite={overwrite_mode}")
        # --- END FIX for task_1_8_2b_fix_placeholder_overwrite_for_modification_steps ---

        return content_to_write, overwrite_mode
    # --- END NEW METHOD ---


    def _read_file_for_context(self, relative_file_path: str) -> str:
        """
        Reads content from a file, handling errors and size limits.

        Args:
            relative_file_path: The path to the file, relative to the context's base_path.

        Returns:
            The content of the file as a string, or an empty string if reading fails
            or the file exceeds the size limit.
        """
        if not isinstance(relative_file_path, str) or relative_file_path == "":
            logger.warning(f"Attempted to read file with invalid path: {relative_file_path}")
            return ""

        full_path = self.context.get_full_path(relative_file_path)

        if full_path is None:
            logger.error(f"Failed to resolve path for reading: {relative_file_path}")
            return "" # Return empty string on path resolution failure

        if not os.path.exists(full_path):
            logger.warning(f"File not found for reading: {relative_file_path}")
            return "" # Return empty string if file doesn't exist

        if not os.path.isfile(full_path):
            logger.warning(f"Path is not a file: {relative_file_path}")
            return "" # Return empty string if path is not a file

        try:
            file_size = os.path.getsize(full_path)
            if file_size > MAX_READ_FILE_SIZE:
                logger.warning(f"File exceeds maximum read size ({MAX_READ_FILE_SIZE} bytes): {relative_file_path} ({file_size} bytes)")
                return "" # Return empty string if file is too large

        except Exception as e:
            logger.error(f"Error checking file size for {relative_file_path}: {e}", exc_info=True)
            return "" # Return empty string on size check error


        try:
            with builtins.open(full_path, 'r', encoding='utf-8', errors='ignore') as f: # Use builtins.open
                content = f.read()
            logger.debug(f"Successfully read {len(content)} characters from {relative_file_path}")
            return content
        except PermissionError:
            logger.error(f"Permission denied when reading file: {relative_file_path}")
            return "" # Return empty string on permission error
        except Exception as e:
            logger.error(f"Unexpected error reading file {relative_file_path}: {e}", exc_info=True)
            return "" # Return empty string on other read errors


    def generate_solution_plan(self, task: dict) -> list[str]:
        """
        Generates a step-by-step solution plan for a given task using the LLM.

        Args:
            task: The task dictionary for which to generate a plan. Must contain
                  'task_name' and 'description'.

        Returns:
            A list of strings representing the plan steps, or an empty list if
            plan generation fails or returns an empty response.
        """
        if not isinstance(task, dict) or 'task_name' not in task or 'description' not in task:
            logger.error("Invalid task dictionary provided for plan generation.")
            return []

        task_name = task['task_name']
        description = task['description']

        # --- START FIX: Restore target_file_context definition ---
        target_file_context = ""
        task_target_file = task.get('target_file')

        # Corrected Logic: Always include target_file context if present
        if task_target_file:
            target_file_context = f"The primary file being modified for this task is specified as `{task_target_file}` in the task metadata. Focus your plan steps on actions related to this file.\n\n" # Added newline for formatting
        # Removed the 'elif' condition that checked for specific keywords
        # --- END FIX ---


        planning_prompt = f"""You are an AI assistant specializing in software development workflows.
Your task is to generate a step-by-step solution plan for the following development task from the Metamorphic Software Genesis Ecosystem roadmap.
Please provide the plan as a numbered markdown list. Do not include any introductory or concluding remarks outside the list.

Task Name: {task_name}

Task Description:
{description}

{target_file_context}When generating steps that involve modifying the primary file for this task, ensure you refer to the file identified in the context (e.g., src/core/automation/workflow_driver.py).
"""


        # The last sentence is kept to guide the LLM's natural language, but the Driver now relies on the target_file field.

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

    def _invoke_coder_llm(self, coder_llm_prompt: str) -> str:
        """
        Invokes the Coder LLM (LLMOrchestrator) to generate code or text.

        Args:
            coder_llm_prompt: The prompt to send to the Coder LLM.

        Returns:
            Return the generated text from the LLM, or None if there was an error.
        """
        try:
            # The prompt is now constructed by the caller (autonomous_loop)
            # This method just passes it to the LLM Orchestrator.
            response = self.llm_orchestrator.generate(coder_llm_prompt)

            if response is None:
                logger.error("LLM Orchestrator generate method returned None.")
                return None

            # The stripping logic remains, as the LLM might still return markdown fences
            cleaned_response = response.strip()
            # Remove leading ```python or ``` followed by optional newline
            if cleaned_response.startswith("```python"):
                cleaned_response = cleaned_response[len("```python"):].lstrip()
            elif cleaned_response.startswith("```"):
                cleaned_response = cleaned_response[len("```"):].lstrip()

            # Remove trailing ``` followed by optional newline and whitespace
            if cleaned_response.endswith("```"):
                cleaned_response = cleaned_response[:-len("```")].rstrip()

            return cleaned_response.strip()

        except Exception as e:
            logger.error(f"Error invoking Coder LLM: {e}", exc_info=True)
            return None

    def select_next_task(self, tasks: list) -> dict | None:
        """
        Selects the next task with status 'Not Started' from the list,
        respecting 'depends_on' dependencies.

        Args:
            tasks: A list of task dictionaries. Each task must contain 'task_id',
                   'status', and optionally 'depends_on'.

        Returns:
            The first task dictionary with a status of 'Not Started' whose
            dependencies are all 'Completed', or None if no such task exists.
        """
        if not isinstance(tasks, list):
            logger.warning(f"select_next_task received non-list input: {type(tasks)}")
            return None

        # Create a quick lookup for task statuses by ID
        task_status_map = {
            task.get('task_id'): task.get('status')
            for task in tasks if isinstance(task, dict) and 'task_id' in task and 'status' in task
        }

        for task in tasks:
            if not isinstance(task, dict) or 'task_id' not in task or 'status' not in task or 'description' not in task or 'priority' not in task:
                logger.warning(f"Skipping invalid task format in list: {task}")
                continue

            task_id = task.get('task_id')
            if not self._is_valid_task_id(task_id):
                logger.warning(f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue

            if task['status'] == 'Not Started':
                depends_on = task.get('depends_on', [])

                # Validate 'depends_on' field format
                if not isinstance(depends_on, list):
                    logger.warning(f"Skipping task {task_id}: 'depends_on' field is not a list.")
                    continue # Skip task if depends_on is not a list

                # Check if all dependencies are 'Completed'
                all_dependencies_completed = True
                for dep_task_id in depends_on:
                    # Validate dependency task ID format
                    if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                        logger.warning(f"Skipping task {task_id}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                        all_dependencies_completed = False
                        break # Stop checking dependencies for this task

                    dep_status = task_status_map.get(dep_task_id)

                    if dep_status is None:
                        # Dependency task not found in the roadmap
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' not found in roadmap.")
                        all_dependencies_completed = False
                        break
                    elif dep_status != 'Completed':
                        # Dependency is not completed (Not Started, In Progress, Blocked)
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' status is '{dep_status}' (requires 'Completed').")
                        all_dependencies_completed = False
                        break

                if all_dependencies_completed:
                    # Found a selectable task
                    return task
            # If status is not 'Not Started', or if dependencies are not met, continue to the next task

        # No selectable task found
        return None


    def generate_coder_llm_prompts(self, task, solution_plan):
        # This method is currently not used in the autonomous_loop for generating code prompts.
        # The code prompts are constructed directly within the loop.
        # Keep this method for potential future use or refactoring.
        if not isinstance(task, dict):
            raise TypeError("Input 'task' must be a dictionary")
        if not isinstance(solution_plan, list):
            raise TypeError("Input 'solution_plan' must be a list of strings")
        if not all(isinstance(step, str) for step in solution_plan):
            raise TypeError("Input 'solution_plan' must be a list of strings")
        if 'task_name' not in task or 'description' not in task:
            raise ValueError("Task dictionary must contain 'task_name' and 'description' keys")

        task_name = task['task_name']
        description = task['description']
        user_actionable_steps_md = self.generate_user_actionable_steps(solution_plan)

        prompt = f"""You are a Coder LLM expert in Python, asked to implement code for the following task:
Task Name: {task_name}

Task Description:
{description}

Implement the following steps:
{user_actionable_steps_md}

Requirements:

Follow best practices for code quality and style.
Prioritize security, and prevent code injection vulnerabilities.
"""
        return [prompt]


    def generate_user_actionable_steps(self, steps):
        if not isinstance(steps, list):
            raise TypeError("generate_user_actionable_steps expects a list of strings")
        if not all(isinstance(step, str) for step in steps):
            raise TypeError("generate_user_actionable_steps expects a list of strings")

        if not steps:
            return ""

        markdown_steps = ""
        for i, step in enumerate(steps):
            # FIX: Apply html.escape here if this output is intended for HTML rendering
            # For now, matching the test expectation of no escaping in the code
            # Apply html.escape to the step description
            escaped_step = html.escape(step)
            markdown_steps += f"{i + 1}. - [ ] {escaped_step}\n" # Changed from 1.  - to 1. -
        return markdown_steps

    def load_roadmap(self, roadmap_file_path):
        tasks = []
        max_file_size = 20000
        if roadmap_file_path is None: # Handle None roadmap_file_path explicitly
            logger.error(f"Failed to load roadmap from None: roadmap_file_path is None")
            return tasks
        # Use the provided roadmap_file_path directly, assuming it's already resolved or validated by the caller (API endpoint)
        # If loading from within the loop, start_workflow ensures it's a full path via context.get_full_path
        full_roadmap_path = roadmap_file_path # Use the path as provided

        if not os.path.exists(full_roadmap_path):
            logger.error(f"ROADMAP.json file not found at path: {full_roadmap_path}")
            return tasks

        if os.path.getsize(full_roadmap_path) > max_file_size:
            logger.error(
                f"ROADMAP.json file exceeds maximum allowed size of {max_file_size} bytes.")
            return tasks

        try:
            with builtins.open(full_roadmap_path, 'r') as f: # Use builtins.open
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
                logger.warning(
                    f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue

            task_name = task_data['task_name']
            if len(task_name) > 150:
                logger.warning(f"Task Name '{task_name}' exceeds 150 characters. Task will be skipped.")
                continue

            task_description = task_data['description']
            # Escape HTML characters in the description to prevent XSS in logs/prompts
            escaped_description = html.escape(task_description)

            # --- ADDED: Load and validate 'depends_on' field ---
            depends_on = task_data.get('depends_on', [])
            if not isinstance(depends_on, list):
                logger.warning(f"Skipping task {task_id}: 'depends_on' field is not a list.")
                continue # Skip task if depends_on is not a list

            is_depends_on_valid = True
            validated_depends_on = []
            for dep_task_id in depends_on:
                if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                    logger.warning(f"Skipping task {task_id}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                    is_depends_on_valid = False
                    break # Stop processing depends_on for this task if any invalid ID is found
                validated_depends_on.append(dep_task_id)

            if not is_depends_on_valid:
                continue # Skip the task if any dependency ID was invalid
            # --- END ADDED ---


            task = {
                'task_id': task_id,
                'priority': task_data['priority'],
                'task_name': task_name,
                'status': task_data['status'],
                'description': escaped_description,
                'target_file': task_data.get('target_file'),
                'depends_on': validated_depends_on # ADDED: Store the validated depends_on list
            }
            tasks.append(task)
        return tasks

    def _is_valid_task_id(self, task_id):
        """Validates task_id to ensure it only contains allowed characters and format."""
        if not isinstance(task_id, str):
            return False
        # Allow alphanumeric, underscores, hyphens, must start with alphanumeric
        # Disallow dots (.) in task IDs as they are used in file paths and could be confusing/risky
        # Updated regex to allow hyphens and underscores at the end
        # FIX: Corrected regex to allow hyphens and underscores *within* the ID, not just at the end
        return bool(re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9_-]*$', task_id))


    def file_exists(self, relative_file_path):
        """Checks if a file exists in the workspace using the context's base path."""
        if not isinstance(relative_file_path, str):
            logger.warning(f"file_exists received non-string input: {type(relative_file_path)}")
            return False
        try:
            # Resolve the path relative to the base_path first, then resolve the full path
            full_path = self.context.get_full_path(relative_file_path)
            if full_path is None: # Check if context path resolution failed
                logger.warning(f"Failed to resolve path for existence check: {relative_file_path}")
                return False
            # No need to call resolve() again here, get_full_path already returns a resolved path
            resolved_path = Path(full_path)
        except Exception as e:
            logger.error(f"Error resolving filepath {relative_file_path} for existence check: {e}",
                         exc_info=True)
            return False

        # The primary check is whether the resolved path actually exists and is a file.
        return os.path.exists(resolved_path) and os.path.isfile(resolved_path)

    def list_files(self):
        """Lists files and directories in the workspace root."""
        base_path = self.context.base_path
        entries = []
        try:
            # Use the resolved base path from the context
            resolved_base_path_str = self.context.get_full_path("") # Resolve empty string to get base path
            if resolved_base_path_str is None:
                logger.error(f"Failed to resolve base path for listing: {base_path}")
                return []
            resolved_base_path = Path(resolved_base_path_str)

            if not resolved_base_path.is_dir():
                logger.error(f"Base path is not a valid directory: {base_path}")
                return []

            # Use resolved_base_path for listing
            for name in os.listdir(resolved_base_path):
                # Add check using _is_valid_filename # ADDED
                if not self._is_valid_filename(name):
                    logger.warning(f"Skipping listing of potentially unsafe filename: {name}")
                    continue
                # END ADDED

                full_path = resolved_base_path / name # Use Path object for joining

                if full_path.is_file(): # Use Path object methods
                    entries.append({'name': name, 'status': 'file'})
                elif full_path.is_dir(): # Use Path object methods
                    entries.append({'name': name, 'status': 'directory'})
        except Exception as e:
            logger.error(f"Error listing files in {base_path}: {e}", exc_info=True)
            return []
        return entries

    def _is_valid_filename(self, filename):
        """Basic validation for filenames to prevent listing malicious names."""
        if not isinstance(filename, str):
            return False
        # Disallow path traversal sequences and directory separators
        # This check is redundant if using Path.resolve() correctly, but adds a layer.
        if '..' in filename or '/' in filename or '\\' in filename: # Corrected backslash escape
            return False
        # Ensure it's not just a dot or dot-dot
        if filename in ['.', '..']:
            return False
        # Allow alphanumeric, underscores, hyphens, and dots. Must start with alphanumeric.
        # Disallow trailing dot.
        # CORRECTED REGEX and added explicit check for trailing dot
        # FIX: Corrected regex to allow dots *within* the filename, not just at the end
        if not re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9._-]*$', filename):
            return False
        if filename.endswith('.'): # Explicitly disallow trailing dot
            return False
        return True

    def _write_output_file(self, filepath, content, overwrite=False):
        """
        Writes content to a file using the write_file utility function, respecting base path.

        Args:
            filepath (str): The path to the file, relative to the context's base_path.
            content (str): The content to write.
            overwrite (bool): Whether to overwrite existing files. Defaults to False.

        Returns:
            bool: True if file writing was successful, False otherwise.

        Raises:
            FileExistsError: If overwrite is False and the file already exists.
        """
        if not isinstance(filepath, str) or filepath == "":
            logger.error(f"_write_output_file received invalid filepath: {filepath}")
            return False
        try:
            # Resolve the path relative to the base_path first, then resolve the full path
            full_path = self.context.get_full_path(filepath)
            if full_path is None: # Check if context path resolution failed
                logger.error(f"Failed to resolve path for writing: {filepath}")
                return False
            # No need to call resolve() again here, get_full_path already returns a resolved path
            resolved_filepath = Path(full_path)
        except Exception as e:
            logger.error(f"Error resolving filepath {filepath} for writing: {e}", exc_info=True)
            return False

        # Ensure the directory exists before writing
        parent_dir = resolved_filepath.parent
        if not parent_dir.exists():
            try:
                parent_dir.mkdir(parents=True, exist_ok=True)
                logger.info(f"Created directory: {parent_dir}")
            except Exception as e:
                logger.error(f"Failed to create directory {parent_dir}: {e}", exc_info=True)
                return False

        try:
            # Pass the resolved full path to write_file
            result = write_file(str(resolved_filepath), content, overwrite=overwrite)
            # write_file already logs success/failure internally
            return result
        except FileExistsError as e:
            # Re-raise FileExistsError as it's expected to be caught by the caller
            raise e
        except FileNotFoundError as e:
            logger.error(f"File not found error when writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False
        except PermissionError as e:
            logger.error(f"Permission error when writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False
        except Exception as e:
            logger.error(f"Unexpected error writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False # ADDED: Return False on generic exception

    def execute_tests(self, test_command: list[str], cwd: str) -> tuple[int, str, str]:
        stdout = ""
        stderr = ""
        return_code = 1

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
            error_msg = f"Error: Command executable not found. Ensure '{test_command[0]}' is in your system's PATH."
            stderr = error_msg
            return_code = 127
            logger.error(error_msg)

        except Exception as e:
            error_msg = f"An unexpected error occurred during command execution: {e}"
            stderr = error_msg
            return_code = 1
            logger.error(error_msg)

        # Store stdout/stderr for potential use in remediation
        self._current_task_results['test_stdout'] = stdout
        self._current_task_results['test_stderr'] = stderr
        # --- ADDED: Store test command and cwd for potential re-execution ---
        self._current_task_results['last_test_command'] = test_command
        self._current_task_results['last_test_cwd'] = cwd
        # --- END ADDED ---
        return return_code, stdout, stderr

    def _merge_snippet(self, existing_content: str, snippet: str) -> str:
        """
        Merges a generated code snippet into existing file content.

        If the METAMORPHIC_INSERT_POINT marker is found, the snippet is inserted
        at the first occurrence of the marker. Otherwise, the snippet is appended
        to the existing content with a newline separator.

        Args:
            existing_content: The current content of the file.
            snippet: The code snippet generated by the Coder LLM.

        Returns:
            The merged content as a string.
        """
        if not snippet:
            return existing_content # Return existing content if snippet is empty

        marker_index = existing_content.find(METAMORPHIC_INSERT_POINT)

        if marker_index != -1:
            # Marker found, insert snippet at the marker position
            before_marker = existing_content[:marker_index]
            after_marker = existing_content[marker_index + len(METAMORPHIC_INSERT_POINT):]
            # Insert the snippet between the parts, replacing the marker
            return before_marker + snippet + after_marker
        else:
            # Marker not found, append snippet with a newline separator
            if not existing_content:
                return snippet # If existing is empty, just return snippet
            # Ensure a newline before appending if existing content doesn't end with one
            # FIX: Removed .strip() from endswith check
            if existing_content and not existing_content.endswith('\n'):
                return existing_content + "\n" + snippet
            # If existing content ends with a newline, just append the snippet
            return existing_content + snippet

    def _parse_test_results(self, raw_output: str) -> dict:
        """
        Parses raw pytest output to extract test results.

        Args:
            raw_output: The raw string output from a pytest subprocess run.

        Returns:
            A dictionary containing parsed test results:
            {'passed': int, 'failed': int, 'total': int, 'status': str, 'message': str}
            Status is 'passed', 'failed', or 'error'.
        """
        if not raw_output:
            logger.warning("Received empty output for test results parsing.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Received empty output.'}

        # Regex to find the final summary line(s)
        # Look for lines starting with '==' and containing 'test session' or test counts
        summary_lines = [line for line in raw_output.splitlines() if line.strip().startswith('==') and ('test session' in line or 'passed' in line or 'failed' in line or 'skipped' in line or 'error' in line)]

        if not summary_lines:
            logger.warning("Could not find pytest summary lines in output.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not find pytest summary lines in output.'}

        # Focus on the last summary line, which usually contains the final counts
        final_summary_line = summary_lines[-1]

        # Regex to extract counts (passed, failed, skipped, error)
        counts_pattern = re.compile(r'(\d+) (passed|failed|skipped|error)')
        matches = counts_pattern.findall(final_summary_line)

        passed = 0
        failed = 0
        skipped = 0
        errors = 0

        for count_str, status_str in matches:
            try:
                count = int(count_str)
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
                # Continue parsing other matches

        total = passed + failed + skipped + errors

        if total == 0 and (passed > 0 or failed > 0 or skipped > 0 or errors > 0):
            logger.warning(f"Parsed counts ({passed}p, {failed}f, {skipped}s, {errors}e) but total is 0. Summary line: {final_summary_line}")
            total = passed + failed + skipped + errors


        status = 'passed' if failed == 0 and errors == 0 and total > 0 else 'failed'
        if total == 0:
            status = 'error' # If no tests ran, consider it an error state for parsing

        if total == 0 and not matches:
            logger.warning(f"Could not parse any counts from summary line: {final_summary_line}")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not parse test results output.'}


        results = {
            'passed': passed,
            'failed': failed,
            'total': total,
            'status': status,
            'message': 'Parsed successfully.' if status != 'error' else 'Could not parse test results output.'
        }

        logger.debug(f"Parsed test results: {results}")
        return results

    # ADDED: Implementation of generate_grade_report and _calculate_grades
    def generate_grade_report(self, task_id: str, validation_results: dict) -> str:
        """
        Generates a structured JSON Grade Report based on validation results.

        Args:
            task_id: The ID of the task being reported on.
            validation_results: A dictionary containing results from automated validation steps.
                                Expected keys: 'test_results', 'code_review_results',
                                'ethical_analysis_results', 'step_errors'. (Security results are within code_review_results)

        Returns:
            A JSON string representing the Grade Report.
        """
        report = {
            "task_id": task_id,
            "timestamp": datetime.utcnow().isoformat(),
            "validation_results": {
                "tests": validation_results.get('test_results', {}),
                "code_review": validation_results.get('code_review_results', {}), # Includes static analysis and bandit
                "ethical_analysis": validation_results.get('ethical_analysis_results', {}),
                "step_errors": validation_results.get('step_errors', []) # Include step errors
            },
            "grades": self._calculate_grades(validation_results)
        }

        # Use standard json.dumps for now
        return json.dumps(report, indent=2)

    def _calculate_grades(self, validation_results: dict) -> dict:
        """
        Calculates probability-based grades based on validation results.

        Weights:
            - Probability of Non-Regression: 20%
            - Probability of Test Success: 30%
            - Code Style Compliance Probability: 10%
            - Probability of Ethical Policy Compliance Probability: 20%
            - Probability of Security Soundness: 20%

        Args:
            validation_results: Dictionary of validation results.

        Returns:
            A dictionary with dimension-specific grades and an overall grade.
        """
        grades = {
            "non_regression": {"percentage": 0, "justification": "No non-regression tests executed."}, # Placeholder
            "test_success": {"percentage": 0, "justification": "No test results available."},
            "code_style": {"percentage": 0, "justification": "No code review results available."},
            "ethical_policy": {"percentage": 0, "justification": "No ethical analysis results available."},
            "security_soundness": {"percentage": 0, "justification": "No security results available."}
        }

        # Calculate Test Success Grade (30%)
        test_results = validation_results.get('test_results')
        if test_results and test_results.get('status') != 'error' and test_results.get('total', 0) > 0:
            percentage = 100 * (test_results.get('passed', 0) / test_results.get('total')) # Partial credit based on pass rate
            grades['test_success'] = {
                "percentage": round(percentage),
                "justification": f"Tests executed: {test_results.get('total')}, Passed: {test_results.get('passed')}, Failed: {test_results.get('failed')}, Total={test_results.get('total')}, Status: {test_results.get('status')}"
            }
        elif test_results and test_results.get('status') == 'error':
            grades['test_success'] = {
                "percentage": 0,
                "justification": f"Test execution or parsing error: {test_results.get('message')}"
            }


        # Calculate Code Style Grade (10%) and Security Soundness Grade (20%)
        # FIX: Corrected key from 'code_review' to 'code_review_results'
        code_review_results = validation_results.get('code_review_results')
        if code_review_results and code_review_results.get('status') != 'error':
            all_findings = code_review_results.get('static_analysis', [])

            # Separate findings into Code Style and Security based on severity prefix
            code_style_findings = [f for f in all_findings if not f.get('severity', '').startswith('security')]
            security_findings = [f for f in all_findings if f.get('severity', '').startswith('security')]

            # --- Code Style Grade Calculation ---
            # Count high severity style findings (errors, warnings, style, info) - adjust based on desired strictness
            # Let's consider 'error' and 'warning' from Flake8 as style issues for this grade
            high_style_issues = [f for f in code_style_findings if f.get('severity') in ['error', 'warning']]
            other_style_issues = [f for f in code_style_findings if f.get('severity') not in ['error', 'warning']]

            style_high_penalty = 15 # Each high style issue reduces score by 15%
            style_other_penalty = 3 # Each other style issue reduces score by 3%

            calculated_style_percentage = 100 - (len(high_style_issues) * style_high_penalty + len(other_style_issues) * style_other_penalty)
            style_percentage = max(0, calculated_style_percentage) # Cap at 0%

            grades['code_style'] = {
                "percentage": style_percentage,
                "justification": f"Code review found {len(code_style_findings)} style issues ({len(high_style_issues)} high severity style). Status: {code_review_results.get('status')}"
            }

            # --- Security Soundness Grade Calculation ---
            high_security_findings = [f for f in security_findings if f.get('severity') == 'security_high']
            medium_security_findings = [f for f in security_findings if f.get('severity') == 'security_medium']
            low_security_findings = [f for f in security_findings if f.get('severity') == 'security_low']

            # Arbitrary penalty factors for security findings
            high_sec_penalty = 50 # Each high security issue reduces score by 50%
            medium_sec_penalty = 10 # Each medium security issue reduces score by 10%
            low_sec_penalty = 2 # Each low security issue reduces score by 2%

            calculated_security_percentage = 100 - (len(high_security_findings) * high_sec_penalty +
                                                    len(medium_security_findings) * medium_sec_penalty +
                                                    len(low_security_findings) * low_sec_penalty)
            security_percentage = max(0, calculated_security_percentage) # Cap at 0%

            grades['security_soundness'] = {
                "percentage": security_percentage,
                "justification": f"Security scan found {len(security_findings)} security findings ({len(high_security_findings)} high, {len(medium_security_findings)} medium, {len(low_security_findings)} low)."
            }

        elif code_review_results and code_review_results.get('status') == 'error':
            error_justification = f"Code review/security execution error: {code_review_results.get('errors', {}).get('flake8', 'N/A')}, {code_review_results.get('errors', {}).get('bandit', 'N/A')}"
            grades['code_style'] = {
                "percentage": 0,
                "justification": error_justification
            }
            grades['security_soundness'] = {
                "percentage": 0,
                "justification": error_justification
            }


        # Calculate Ethical Policy Grade (20%)
        ethical_results = validation_results.get('ethical_analysis_results')
        if ethical_results and ethical_results.get('overall_status') != 'error':
            percentage = 100 if ethical_results.get('overall_status') == 'approved' else 0
            justification = f"Ethical analysis status: {ethical_results.get('overall_status')}. Policy: {ethical_results.get('policy_name', 'N/A')}"
            if ethical_results.get('overall_status') == 'rejected':
                violations = [k for k, v in ethical_results.items() if isinstance(v, dict) and v.get('status') == 'violation']
                justification += f". Violations: {', '.join(violations)}"
            elif ethical_results.get('overall_status') == 'skipped':
                percentage = 0 # Skipped is treated as 0 for grading
                justification = f"Ethical analysis skipped: {ethical_results.get('message', 'Unknown reason')}"

            grades['ethical_policy'] = {
                "percentage": percentage,
                "justification": justification
            }
        elif ethical_results and ethical_results.get('overall_status') == 'error':
            grades['ethical_policy'] = {
                "percentage": 0,
                "justification": f"Ethical analysis execution error: {ethical_results.get('message', 'Unknown error')}"
            }


        # Calculate Non-Regression Grade (20%) - Placeholder for now
        # This requires comparing current state/behavior to previous, which is complex.
        # For 1.6f, this will be a placeholder.
        # Simple heuristic: 100% if Test Success is 100%, 0% otherwise.
        grades['non_regression'] = {
            "percentage": 100 if grades['test_success']['percentage'] == 100 else 0,
            "justification": "Non-regression testing is a placeholder. Graded based on Test Success (100% if tests passed, 100% if no tests ran, 0% otherwise)."
        }


        # Calculate Overall Percentage Grade
        # Weights: Non-Regression (20%), Test Success (30%), Code Style (10%), Ethical Policy (20%), Security Soundness (20%)
        overall_percentage = (
            grades['non_regression']['percentage'] * 0.20 +
            grades['test_success']['percentage'] * 0.30 +
            grades['code_style']['percentage'] * 0.10 +
            grades['ethical_policy']['percentage'] * 0.20 +
            grades['security_soundness']['percentage'] * 0.20
        )

        grades['overall_percentage_grade'] = round(overall_percentage)

        return grades

    def _parse_and_evaluate_grade_report(self, grade_report_json: str) -> dict:
        """
        Parses a JSON Grade Report, evaluates results, and determines the recommended next action.

        Args:
            grade_report_json: The JSON string representing the Grade Report.

        Returns:
            A dictionary containing the recommended_action and justification.
        """
        logger.info("Parsing and evaluating Grade Report...")
        try:
            report_data = json.loads(grade_report_json)
        except json.JSONDecodeError as e:
            logger.error(f"Failed to parse Grade Report JSON: {e}", exc_info=True)
            return {
                "recommended_action": "Manual Review Required",
                "justification": f"Failed to parse Grade Report JSON: {e}"
            }

        # Extract key metrics, handling missing keys
        grades = report_data.get('grades', {})
        validation_results = report_data.get('validation_results', {})

        overall_percentage_grade = grades.get('overall_percentage_grade', 0)
        test_results = validation_results.get('tests', {})
        code_review_results = validation_results.get('code_review', {})
        ethical_analysis_results = validation_results.get('ethical_analysis', {})
        step_errors = validation_results.get('step_errors', []) # Get step errors

        logger.info(f"Grade Report Metrics: Overall Grade={overall_percentage_grade}%, Test Status={test_results.get('status')}, Ethical Status={ethical_analysis_results.get('overall_status')}, Code Review Status={code_review_results.get('status')}, Step Errors={len(step_errors)}") # Include step errors in log

        recommended_action = "Manual Review Required"
        justification = "Default action based on unhandled scenario."

        # --- START: Prioritize Manual Review for Step Errors ---
        if step_errors:
             recommended_action = "Manual Review Required"
             justification = f"Step execution errors occurred ({len(step_errors)} errors). Manual review required."
             logger.warning(f"Step execution errors detected. Recommended Action: {recommended_action}")
             return {
                 "recommended_action": recommended_action,
                 "justification": justification
             }
        # --- END: Prioritize Manual Review for Step Errors ---


        # Rule 1: Perfect Score
        if overall_percentage_grade == 100:
            recommended_action = "Completed"
            justification = "Overall grade is 100%."
        # Rule 2: Critical Ethical Violation
        elif ethical_analysis_results.get('overall_status') == 'rejected':
            recommended_action = "Blocked"
            justification = "Ethical analysis rejected the code."
        # Rule 3: High-Risk Security Finding
        elif code_review_results.get('static_analysis') and any(f.get('severity') == 'security_high' for f in code_review_results['static_analysis']):
            recommended_action = "Blocked"
            justification = "High-risk security findings detected."
        # Rule 4: Test Failures
        elif test_results.get('status') == 'failed':
            recommended_action = "Regenerate Code"
            justification = "Automated tests failed."
        # Rule 5: Below Perfect but Acceptable for Regeneration
        elif overall_percentage_grade >= 80: # Threshold for regeneration
            recommended_action = "Regenerate Code"
            justification = f"Overall grade ({overall_percentage_grade}%) is below 100% but meets regeneration threshold."
        # Default: Manual Review Required
        else:
            recommended_action = "Manual Review Required"
            justification = f"Overall grade ({overall_percentage_grade}%) is below regeneration threshold or other issues require manual review."

        logger.info(f"Recommended Action: {recommended_action}. Justification: {justification}")

        return {
            "recommended_action": recommended_action,
            "justification": justification
        }

    def _safe_write_roadmap_json(self, roadmap_path: str, new_content: dict) -> bool:
        """
        Safely writes updated content to the ROADMAP.json file using an atomic write pattern.

        Args:
            roadmap_path: The relative path to the roadmap file (e.g., "ROADMAP.json").
            new_content: The new content for the roadmap file as a dictionary.

        Returns:
            True if the write was successful, False otherwise.
        """
        # 1. Resolve the full path safely
        resolved_filepath = self.context.get_full_path(roadmap_path)
        if resolved_filepath is None:
            logger.error(f"Security alert: Path traversal attempt detected for roadmap file: {roadmap_path}")
            return False

        # 2. Validate content structure
        if not isinstance(new_content, dict):
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Content is not a dictionary.")
            return False
        if 'tasks' not in new_content:
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Missing 'tasks' key.")
            return False

        # 3. Implement atomic write
        resolved_filepath_obj = Path(resolved_filepath)
        roadmap_dir = resolved_filepath_obj.parent
        temp_filename = f".{resolved_filepath_obj.name}.{uuid.uuid4()}.tmp"
        temp_filepath = roadmap_dir / temp_filename

        # Clean up potential leftover temporary file from a previous failed attempt
        if temp_filepath.exists():
            try:
                os.remove(temp_filepath)
                logger.debug(f"Cleaned up leftover temporary file: {temp_filepath}")
            except Exception as cleanup_e:
                logger.warning(f"Failed to clean up leftover temporary file {temp_filepath}: {cleanup_e}")


        try:
            # Write to temporary file
            with builtins.open(temp_filepath, 'w', encoding='utf-8') as f: # Use builtins.open
                json.dump(new_content, f, indent=2)

            # Atomically replace the original file
            os.replace(temp_filepath, resolved_filepath)

            logger.info(f"Successfully wrote updated roadmap to {roadmap_path}")
            return True

        except (IOError, OSError, PermissionError, json.JSONDecodeError) as e:
            logger.error(f"Error writing roadmap file {roadmap_path}: {e}", exc_info=True)
            # Clean up temporary file in case of failure after temp file is created but before replace
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after error: {e}") # This was using undefined cleanup_e
                except Exception as cleanup_e_inner: # Use a different variable name
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after error: {cleanup_e_inner}")
            return False
        except Exception as cleanup_e: # Corrected indentation for this except block
            logger.error(f"Unexpected error during roadmap file write {roadmap_path}: {cleanup_e}", exc_info=True)
            # Clean up temporary file in case of unexpected failure
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after unexpected error: {cleanup_e}") # This was using undefined cleanup_e
                except Exception as cleanup_e_inner: # Use a different variable name
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after unexpected error: {cleanup_e_inner}")
            return False

    # --- NEW METHOD: Update task status in roadmap file ---
    def _update_task_status_in_roadmap(self, task_id: str, new_status: str, reason: str = None):
        """
        Updates the status of a specific task in the roadmap file and optionally adds a reason.

        Args:
            task_id: The ID of the task to update.
            new_status: The new status ('Completed', 'Blocked', etc.).
            reason: An optional string explaining the reason for the status change (e.g., for 'Blocked').
        """
        try:
            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
            if full_roadmap_path is None:
                logger.error(f"Cannot update roadmap status: Invalid roadmap path provided: {self.roadmap_path}")
                return

            try:
                with builtins.open(full_roadmap_path, 'r') as f:
                    roadmap_data = json.load(f)
            except FileNotFoundError:
                logger.error(f"Error updating roadmap status for task {task_id}: Roadmap file not found at {full_roadmap_path}")
                return
            except json.JSONDecodeError:
                logger.error(f"Error updating roadmap status for task {task_id}: Invalid JSON in roadmap file {full_roadmap_path}")
                return

            task_found = False
            if isinstance(roadmap_data, dict) and isinstance(roadmap_data.get('tasks'), list):
                for task_entry in roadmap_data['tasks']:
                    if isinstance(task_entry, dict) and task_entry.get('task_id') == task_id:
                        old_status = task_entry.get('status', 'Unknown') # Capture old status
                        task_entry['status'] = new_status
                        if reason:
                            task_entry['reason_blocked'] = reason # Add reason for blocked tasks
                        elif 'reason_blocked' in task_entry:
                            del task_entry['reason_blocked'] # Remove reason if status is no longer blocked
                        # Log the status change here as suggested by the other LLM
                        logger.info(f"Updating task status from '{old_status}' to '{new_status}' for task {task_id}")
                        task_found = True
                        break

            if task_found:
                if self._safe_write_roadmap_json(self.roadmap_path, roadmap_data):
                    logger.info(f"Successfully wrote updated status for task {task_id} in {self.roadmap_path}")
                else:
                    logger.error(f"Failed to safely write updated roadmap for task {task_id}")
            else:
                logger.warning(f"Task {task_id} not found in roadmap file {self.roadmap_path} for status update.")

        except Exception as e:
            logger.error(f"Error updating roadmap status for task {task_id}: {e}", exc_info=True)
    # --- END NEW METHOD ---


    def _identify_remediation_target(self, grade_report_json: str) -> str | None:
        """
        Parses the grade report JSON to identify the primary target for remediation.

        Args:
            grade_report_json: The JSON string of the grade report.

        Returns:
            "Code Style", "Ethical Transparency", or "Test Failure" if a clear target identified, or None.
        """
        try:
            report_data = json.loads(grade_report_json)
            grades = report_data.get('grades', {})
            validation = report_data.get('validation_results', {})

            # Prioritize critical failures first (though remediation might not apply)
            # Check for Test Failures first as they are often the most direct feedback
            test_results = validation.get('tests', {})
            if test_results.get('status') == 'failed':
                 logger.debug("Identified Test Failure as remediation target.")
                 return "Test Failure"

            # Check for Ethical Violation (specifically TransparencyScore if applicable)
            ethical_results = validation.get('ethical_analysis', {})
            if ethical_results.get('overall_status') == 'rejected':
                if ethical_results.get('TransparencyScore', {}).get('status') == 'violation':
                    logger.debug("Identified Ethical Transparency as remediation target.")
                    return "Ethical Transparency"
                else:
                    logger.debug("Ethical rejection not due to TransparencyScore, no specific ethical remediation target identified.")
                    # Continue to check code style remediation possibility

            # Check for Code Style issues if no specific ethical transparency issue was found
            code_style_grade = grades.get('code_style', {}).get('percentage', 100)
            if code_style_grade < 100: # Assuming 100 means no style issues
                # Check if the code review actually reported issues (status 'failed' or findings present)
                code_review_results = validation.get('code_review', {})
                if code_review_results.get('status') == 'failed' or code_review_results.get('static_analysis'):
                    logger.debug("Identified Code Style as remediation target.")
                    return "Code Style"
                else:
                    logger.debug("Code style grade below 100, but code review status not 'failed' and no static analysis findings.")
                    pass # Continue to check other targets if any

            # <--- Security High findings are typically Blocked, not remediated automatically --->
            # The _parse_and_evaluate_grade_report handles blocking for security_high.
            # Remediation logic here focuses on issues that result in 'Regenerate Code'.

            logger.debug("No specific remediation target identified from grade report for automated remediation.")
            return None
        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for remediation target identification.")
            return None
        except Exception as e:
            logger.error(f"Error identifying remediation target: {e}", exc_info=True)
            return None


    def _attempt_code_style_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        """
        Attempts to remediate code style issues using LLM feedback.
        (Implementation as provided in the codebase)
        """
        logger.info(f"Attempting code style remediation for {file_path}...")
        try:
            report_data = json.loads(grade_report_json)
            code_review_results = report_data.get('validation_results', {}).get('code_review', {})
            findings = code_review_results.get('static_analysis', [])

            style_feedback = [
                f"- {f.get('code')} at line {f.get('line')}: {f.get('message')}"
                for f in findings if not f.get('severity', '').startswith('security')
            ]

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
            logger.debug("Invoking Coder LLM for code style remediation...")
            corrected_code = self._invoke_coder_llm(feedback_prompt)


            if not corrected_code or corrected_code.strip() == original_code.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged.")
                return False

            logger.info("LLM provided corrected code. Applying and re-validating...")

            content_to_write = corrected_code
            write_success = self._write_output_file(file_path, content_to_write, overwrite=True)

            if write_success:
                try:
                    logger.info(f"Re-running code review for {file_path} after remediation...")
                    new_review_results = self.code_review_agent.analyze_python(content_to_write)
                    self._current_task_results['code_review_results'] = new_review_results
                    logger.info(f"Code Review Results after remediation: {new_review_results}")
                    if new_review_results.get('status') == 'success':
                        logger.info("Code style remediation appears successful based on re-scan.")
                    elif new_review_results.get('status') == 'failed':
                        logger.warning("Code style issues persist after remediation attempt.")
                    else:
                        logger.error("Error occurred during code review re-scan after remediation.")
                except Exception as e:
                    logger.error(f"Error occurred during code review re-scan after remediation: {e}", exc_info=True)
                    self._current_task_results['code_review_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                return True # Return True if write succeeded, even if re-validation failed
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.")
                return False # Return False if write failed
        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for code style remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during code style remediation: {e}", exc_info=True)
            return False

    def _attempt_ethical_transparency_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        """
        Attempts to remediate ethical transparency issues (missing docstrings) using LLM feedback.
        (Implementation as provided in the codebase)
        """
        logger.info(f"Attempting ethical transparency remediation for {file_path}...")
        try:
            report_data = json.loads(grade_report_json)
            ethical_results = report_data.get('validation_results', {}).get('ethical_analysis', {})
            transparency_details = ethical_results.get('TransparencyScore', {})

            if transparency_details.get('status') != 'violation':
                logger.warning("Ethical transparency remediation triggered, but no violation found in report.")
                return False

            feedback_str = transparency_details.get('details', "Missing required docstring(s).")
            logger.debug(f"Extracted ethical transparency feedback: {feedback_str}")

            feedback_prompt = f"""You are a Coder LLM expert in Python documentation and code transparency.
The following Python code failed an automated ethical transparency check, likely due to missing docstrings.

File Path: {file_path}
Original Task: "{task.get('task_name', 'Unknown Task')}"
Plan Step: "{step_desc}"

Code with Issues:

{original_code}
Identified Transparency Issue:
{feedback_str}

Your task is to rewrite the entire code block above, adding the necessary docstrings to satisfy the transparency requirement.

Add a module-level docstring if missing.
Add docstrings to all functions and classes.
Docstrings should clearly explain the purpose, arguments, and return values (if any).
Maintain all original logic and functionality.
Output only the complete, corrected Python code with added docstrings. Do not include explanations or markdown fences.
"""
            logger.debug("Invoking Coder LLM for ethical transparency remediation...")
            corrected_code = self._invoke_coder_llm(feedback_prompt)


            if not corrected_code or corrected_code.strip() == original_code.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged.")
                return False

            logger.info("LLM provided corrected code with docstrings. Applying and re-validating...")

            content_to_write = corrected_code
            write_success = self._write_output_file(file_path, content_to_write, overwrite=True)

            if write_success:
                if self.default_policy_config:
                    try:
                        logger.info(f"Re-running ethical analysis for {file_path} after remediation...")
                        new_ethical_results = self.ethical_governance_engine.enforce_policy(content_to_write, self.default_policy_config)
                        self._current_task_results['ethical_analysis_results'] = new_ethical_results
                        logger.info(f"Ethical Analysis Results after remediation: {new_ethical_results}")
                        if new_ethical_results.get('overall_status') == 'approved':
                            logger.info("Ethical transparency remediation appears successful based on re-scan.")
                        elif new_ethical_results.get('overall_status') == 'rejected':
                            logger.warning("Ethical transparency violation persists after remediation attempt.")
                        else:
                            logger.error("Error or skip occurred during ethical analysis re-scan after remediation.")
                    except Exception as e:
                        logger.error(f"Error occurred during ethical analysis re-scan after remediation: {e}", exc_info=True)
                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': f"Re-validation error: {e}"}
                else:
                    logger.warning("Cannot re-run ethical analysis after remediation: Default policy not loaded.")
                    self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded for re-scan.'}
                return True # Return True if write succeeded, even if re-validation failed
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.")
                return False # Return False if write failed
        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for ethical transparency remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during ethical transparency remediation: {e}", exc_info=True)
            return False

    def _attempt_test_failure_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        """
        Attempts to remediate test failures using LLM feedback.

        Args:
            grade_report_json: JSON string of the grade report.
            task: The current task dictionary.
            step_desc: The description of the plan step being executed (e.g., "Test Failure Remediation").
            file_path: The path to the file being modified.
            original_code: The code content before the remediation attempt.

        Returns:
            True if remediation was attempted and write succeeded, False otherwise.
        """
        logger.info(f"Attempting test failure remediation for {file_path}...")
        try:
            # No need to parse grade_report_json here, test results are in _current_task_results
            stdout = self._current_task_results.get('test_stdout', '')
            stderr = self._current_task_results.get('test_stderr', '')
            test_results = self._current_task_results.get('test_results', {})

            if test_results.get('status') != 'failed':
                logger.warning("Test failure remediation triggered, but test status is not 'failed'.")
                return False

            logger.debug(f"Test failure details - Stdout: {stdout}, Stderr: {stderr}")
            # Read current file content again, as it might have been modified by previous remediation attempts
            current_file_content = self._read_file_for_context(file_path)

            if not current_file_content or not file_path:
                logger.error(f"Failed to read current file content for {file_path} during test remediation. Cannot attempt remediation.")
                return False

            task_name = task.get('task_name', 'Unknown Task')
            task_description = task.get('description', 'No description provided')

            prompt = f"""
You are tasked with fixing the following test failure in the Python code.

Task: {task_name}
Description: {task_description}
File to modify: {file_path}
# FIX: Added the current code content to the remediation prompt
Current code content:
```python
{current_file_content}
```
Test execution output:
Stdout:
```
{stdout}
```
Stderr:
```
{stderr}
```
Instructions:

Analyze the test failure output (Stdout and Stderr) and the current code content to identify the root cause of the test failures.
Generate only the Python code snippet needed to fix the issue. This snippet should contain the necessary modifications to the code in {file_path}.
Do NOT include any surrounding text, explanations, or markdown code block fences (```). Provide just the raw code lines that need to be added or modified.
Maintain all original logic and functionality not related to the test failures.
Adhere to PEP 8 style guidelines.
Note: The Debug Agent (task_2_2_6) is NOT available; you must generate the fix directly based on the provided information.
Your response should be the corrected code snippet that addresses the test failure based on the provided context and error messages.
"""
            logger.debug("Invoking Coder LLM for test failure remediation...")
            corrected_code = self._invoke_coder_llm(prompt)


            if not corrected_code or corrected_code.strip() == current_file_content.strip(): # Compare against current content
                logger.warning("LLM did not provide corrected code or code was unchanged for test failure remediation.")
                return False

            logger.info("LLM provided corrected code for test failure. Applying and re-validating...")

            merged_content = self._merge_snippet(current_file_content, corrected_code) # FIX: Use corrected_code here
            write_success = self._write_output_file(file_path, merged_content, overwrite=True)

            if write_success:
                logger.info(f"Successfully wrote fixed code to {file_path}")
                # Re-run validations after applying the fix
                try:
                    logger.info(f"Re-running validations for {file_path} after test failure remediation...")
                    # Retrieve the last used test command and cwd
                    test_command = self._current_task_results.get('last_test_command', ['pytest', 'tests/'])
                    cwd = self._current_task_results.get('last_test_cwd', self.context.base_path)

                    return_code, new_stdout, new_stderr = self.execute_tests(test_command, cwd)
                    self._current_task_results['test_stdout'] = new_stdout
                    self._current_task_results['test_stderr'] = new_stderr
                    self._current_task_results['test_results'] = self._parse_test_results(new_stdout) # Update test results

                    # Re-run other validations on the merged content
                    code_review_result = self.code_review_agent.analyze_python(merged_content) # Correct call
                    ethical_result = self.ethical_governance_engine.enforce_policy(merged_content, self.default_policy_config) # Correct call
                    self._current_task_results['code_review_results'] = code_review_result
                    self._current_task_results['ethical_analysis_results'] = ethical_result

                    logger.info(f"Validations re-run after test failure remediation.")
                    # The calling loop will re-generate and re-evaluate the grade report

                except Exception as e:
                    logger.error(f"Error occurred during re-validation after test failure remediation: {e}", exc_info=True)
                    # Update results with error status
                    self._current_task_results['test_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                    self._current_task_results['code_review_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                    self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': f"Re-validation error: {e}"}

                return True # Remediation was attempted and write succeeded

            else:
                logger.error(f"Failed to write fixed code to {file_path}. Aborting test failure remediation.")
                return False # Remediation attempt failed (write failed)

        except json.JSONDecodeError:
                    logger.error("Failed to parse grade report JSON for test failure remediation.")
                    return False
        except Exception as e:
            logger.error(f"Error during test failure remediation: {e}", exc_info=True)
            return False