import logging
import html
import os
import json
from pathlib import Path
import re
from unittest.mock import MagicMock
from src.cli.write_file import write_file
import subprocess
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
from datetime import datetime
import uuid
import builtins
import spacy
from spacy.matcher import PhraseMatcher
import ast
from typing import List, Dict, Optional, Tuple

from src.core.llm_orchestration import EnhancedLLMOrchestrator

logger = logging.getLogger(__name__)

MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"
MAX_STEP_RETRIES = 2
MAX_IMPORT_CONTEXT_LINES = 200

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
    def __init__(self, base_path):
        self.base_path = base_path
        try:
            self._resolved_base_path = Path(self.base_path).resolve()
        except Exception as e:
            logger.error(f"Error resolving base path '{self.base_path}': {e}", exc_info=True)
            self._resolved_base_path = None

    def get_full_path(self, relative_path):
        if self._resolved_base_path is None:
            logger.error(f"Base path failed to resolve. Cannot resolve relative path '{relative_path}'.")
            return None
        if not isinstance(relative_path, str):
            logger.warning(f"Attempted to resolve path with invalid input type: {type(relative_path)}")
            return None
        try:
            full_requested_path = self._resolved_base_path / relative_path
            resolved_path = full_requested_path.resolve()
            if not str(resolved_path).startswith(str(self._resolved_base_path)):
                logger.warning(f"Path traversal attempt detected during resolution: {relative_path} resolved to {resolved_path}")
                return None
            return str(resolved_path)
        except Exception as e:
            logger.error(f"Error resolving path '{relative_path}' relative to '{self.base_path}': {e}", exc_info=True)
            return None

    def __eq__(self, other):
        if not isinstance(other, Context):
            return NotImplemented
        return self.base_path == other.base_path

    def __repr__(self):
        return f"Context(base_path='{self.base_path}')"

class WorkflowDriver:
    def __init__(self, context: Context):
        self.context = context
        self.tasks = []
        self._current_task_results = {}
        self.remediation_attempts = 0
        self._current_task = {}
        self.task_target_file = None
        self.ethical_governance_engine = EthicalGovernanceEngine()
        self._load_default_policy()
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=MagicMock(),
            ethics_engine=self.ethical_governance_engine
        )
        self.code_review_agent = CodeReviewAgent()

    def _load_default_policy(self):
        default_policy_path = self.context.get_full_path("policies/policy_bias_risk_strict.json")
        if default_policy_path:
            try:
                # Use builtins.open explicitly
                with builtins.open(default_policy_path, 'r') as f:
                     self.default_policy_config = json.load(f)
                logger.info(f"Loaded default ethical policy: {self.default_policy_config.get('policy_name')}")
            except FileNotFoundError:
                 logger.warning(f"Default ethical policy file not found at {default_policy_path}. Ethical analysis will be skipped.")
                 self.default_policy_config = None
            except json.JSONDecodeError:
                 logger.error(f"Invalid JSON in default ethical policy file: {default_policy_path}. Ethical analysis will be skipped.")
                 self.default_policy_config = None
            except Exception as e:
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
            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
            if full_roadmap_path is None:
                logger.error(f"Invalid roadmap path provided: {self.roadmap_path}. Cannot start autonomous loop.")
                return
            self.tasks = self.load_roadmap(full_roadmap_path)
        except Exception as e:
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
        if not isinstance(relative_path, str):
            logger.warning(f"Path validation received invalid input: {relative_path}")
            return None

        resolved_path = self.context.get_full_path(relative_path)

        if resolved_path is None:
            logger.warning(f"Resolved path '{relative_path}' is invalid or outside the allowed context.")

        return resolved_path

    def _resolve_target_file_for_step(self, current_step_description: str, task_target_file_spec: Optional[str], prelim_flags: Dict) -> Optional[str]:
        """
        Determines the single target file for the current step, especially when the task
        specifies multiple target files. It prioritizes explicit mentions in the step
        description from the task's list, then falls back to other determination logic.
        Uses _validate_path for safety.

        Args:
            current_step_description: The description of the current plan step.
            task_target_file_spec: The 'target_file' string from the task definition,
                                   which might be a single file or comma-separated list.
            prelim_flags: Preliminary classification flags for the step.

        Returns:
            The resolved single target file path for the step (absolute and safe), or None.
        """
        is_code_generation_step = prelim_flags.get('is_code_generation_step_prelim', False)
        should_apply_multi_target_logic = is_code_generation_step

        resolved_step_target_file_relative = None
        potential_task_targets = []

        if task_target_file_spec and isinstance(task_target_file_spec, str):
            potential_task_targets = [f.strip() for f in task_target_file_spec.split(',') if f.strip()]

        if len(potential_task_targets) > 1 and should_apply_multi_target_logic:
            logger.debug(
                f"Task has multiple target files listed: {potential_task_targets}. "
                f"Attempting to determine specific target for step: '{current_step_description}'"
            )

            found_in_step_description = False
            step_desc_lower = current_step_description.lower()

            for file_candidate_relative in potential_task_targets:
                normalized_candidate_path_str = Path(file_candidate_relative).as_posix().lower()
                filename_candidate_lower = Path(file_candidate_relative).name.lower()

                if normalized_candidate_path_str in step_desc_lower:
                    resolved_step_target_file_relative = file_candidate_relative
                    logger.info(
                        f"Step description explicitly mentions '{resolved_step_target_file_relative}' "
                        f"from task target list {potential_task_targets}."
                    )
                    found_in_step_description = True
                    break
                elif re.search(r'(?<![a-zA-Z0-9_.-])' + re.escape(filename_candidate_lower) + r'(?![a-zA-Z0-9_.-])', step_desc_lower):
                    resolved_step_target_file_relative = file_candidate_relative
                    logger.info(
                        f"Step description explicitly mentions filename '{filename_candidate_lower}' "
                        f"(from '{resolved_step_target_file_relative}') from task target list {potential_task_targets}."
                    )
                    found_in_step_description = True
                    break

            if not found_in_step_description:
                if potential_task_targets:
                    resolved_step_target_file_relative = potential_task_targets[0]
                    logger.warning(
                        f"Step description '{current_step_description}' does not explicitly mention any file "
                        f"from the task's target list: {potential_task_targets}. "
                        f"Defaulting to the first file: '{resolved_step_target_file_relative}'."
                    )
                else:
                    logger.error(f"Task target file list was unexpectedly empty after parsing for step: '{current_step_description}'")
                    resolved_step_target_file_relative = self._determine_filepath_to_use(current_step_description, None, prelim_flags)

        elif potential_task_targets:
             resolved_step_target_file_relative = self._determine_filepath_to_use(current_step_description, task_target_file_spec, prelim_flags)
        else:
            if task_target_file_spec is not None and task_target_file_spec != "":
                 logger.error(f"Task target file list was unexpectedly empty after parsing for step: '{current_step_description}'")
            resolved_step_target_file_relative = self._determine_filepath_to_use(current_step_description, None, prelim_flags)

        return self._validate_path(resolved_step_target_file_relative)

    def _determine_filepath_to_use(self, step_description: str, task_target_file: str | None, preliminary_flags: dict) -> str | None:
        filepath_from_step = preliminary_flags.get('filepath_from_step')
        is_code_generation_step_prelim = preliminary_flags.get('is_code_generation_step_prelim', False)
        is_test_writing_step_prelim = preliminary_flags.get('is_test_writing_step_prelim', False)
        is_explicit_file_writing_step_prelim = preliminary_flags.get('is_explicit_file_writing_step_prelim', False)

        effective_task_target = None
        if task_target_file and isinstance(task_target_file, str):
             targets = [f.strip() for f in task_target_file.split(',') if f.strip()]
             if targets:
                 effective_task_target = targets[0]

        filepath_to_use = effective_task_target

        if is_code_generation_step_prelim and is_test_writing_step_prelim:
            explicit_test_path_in_step = None
            all_paths_in_step_matches = re.finditer(r'(\S+\.py)', step_description, re.IGNORECASE)
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

        return filepath_to_use

    def _determine_write_operation_details(self, step_description: str, filepath_to_use: str | None, task_target_file: str | None, preliminary_flags: dict) -> tuple[str | None, bool]:
        step_lower = step_description.lower()
        is_explicit_file_writing_step_prelim = preliminary_flags.get('is_explicit_file_writing_step_prelim', False)
        is_research_step_prelim = preliminary_flags.get('is_research_step_prelim', False)
        step_implies_create_new_file = any(re.search(r'\b' + re.escape(keyword) + r'\b', step_lower) for keyword in ["create file", "generate file"])
        resolved_task_target_file = self.context.get_full_path(task_target_file) if task_target_file else None
        is_main_python_target = (resolved_task_target_file is not None and filepath_to_use == resolved_task_target_file and filepath_to_use is not None and filepath_to_use.endswith('.py'))

        conceptual_define_keywords_check_prelim = ["define list", "analyze", "understand", "document decision", "identify list", "define a comprehensive list"]
        is_conceptual_step_for_main_target = is_research_step_prelim or \
                                            any(re.search(r'\b' + re.escape(kw) + r'\b', step_lower) for kw in conceptual_define_keywords_check_prelim)

        content_to_write = None
        overwrite_mode = True

        if is_explicit_file_writing_step_prelim and filepath_to_use:
            if is_main_python_target:
                if step_implies_create_new_file:
                    overwrite_mode = False
                    if filepath_to_use.endswith('.py'):
                         content_to_write = f"# Placeholder content for Python file for step: {step_description}"
                         logger.info(f"Using placeholder for NEW main Python target {filepath_to_use} for step: '{step_description}'.")
                    else:
                         logger.warning(f"Step implies creating main target {filepath_to_use}, but it's not a .py file. Skipping placeholder.")
                         content_to_write = None
                elif is_conceptual_step_for_main_target:
                    logger.info(f"Skipping placeholder write to main Python target {filepath_to_use} for conceptual step: '{step_description}'.")
                    content_to_write = None
                else:
                    logger.info(f"Skipping placeholder write to main Python target {filepath_to_use} for modification step: '{step_description}'. This step should be handled by code generation.")
                    content_to_write = None
            else:
                if step_implies_create_new_file:
                    overwrite_mode = False
                if filepath_to_use.endswith('.py'):
                    content_to_write = f"# Placeholder content for Python file for step: {step_description}"
                else:
                    content_to_write = f"// Placeholder content for step: {step_description}"
                if content_to_write:
                    logger.info(f"Using placeholder content for file: {filepath_to_use} with overwrite={overwrite_mode}")

        return content_to_write, overwrite_mode

    def file_exists(self, path: str) -> bool:
        """
        Checks if a file exists at the given path relative to the base path,
        ensuring the path is within the allowed context.
        """
        if not isinstance(path, str):
            logger.warning(f"file_exists received non-string input: {type(path)}")
            return False
        resolved_path = self.context.get_full_path(path)
        if resolved_path is None:
            logger.warning(f"Failed to resolve path for existence check: {path}")
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
        resolved_base_path_str = self.context.get_full_path(path or "")
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
            for name in os.listdir(resolved_base_path_str):
                if not self._is_valid_filename(name):
                    logger.warning(f"Skipping listing of potentially unsafe filename: {name}")
                    continue

                entry_path = resolved_base_path_obj / name

                try:
                    if entry_path.is_file():
                        entries.append({'name': name, 'status': 'file'})
                    elif entry_path.is_dir():
                        entries.append({'name': name, 'status': 'directory'})
                except Exception as e:
                     logger.warning(f"Error checking status of entry {name} in {path or 'base path'}: {e}", exc_info=True)

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
            escaped_step = html.escape(step)
            formatted_steps.append(f"{i + 1}. - [ ] {escaped_step}")

        return "\n".join(formatted_steps) + ("\n" if formatted_steps else "")

    def autonomous_loop(self):
        if not hasattr(self, 'roadmap_path') or (self.roadmap_path is None):
            logger.error("Roadmap path not set. Cannot start autonomous loop.")
            return

        while True:
            logger.info('Starting autonomous loop iteration')
            self._current_task_results = {}
            self._current_task_results['step_errors'] = []
            self.remediation_attempts = 0
            self.remediation_occurred_in_pass = False

            try:
                full_roadmap_path = self.context.get_full_path(self.roadmap_path)
                if full_roadmap_path is None:
                    logger.error(f"Invalid roadmap path provided: {self.roadmap_path}. Cannot continue autonomous loop.")
                    break
                self.tasks = self.load_roadmap(full_roadmap_path)
            except Exception as e:
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

                        while step_retries <= MAX_STEP_RETRIES:
                            try:
                                logger.info(f"Executing step {step_index + 1}/{len(solution_plan)} (Attempt {step_retries + 1}/{MAX_STEP_RETRIES + 1}): {step}")
                                prelim_flags = self._classify_step_preliminary(step)

                                filepath_to_use = self._resolve_target_file_for_step(step, self.task_target_file, prelim_flags)

                                content_to_write, overwrite_mode = self._determine_write_operation_details(step, filepath_to_use, self.task_target_file, prelim_flags)
                                generated_output = None

                                if prelim_flags['is_test_execution_step_prelim']:
                                    logger.info(f"Step identified as test execution. Running tests for step: {step}")
                                    test_command = ["pytest"]
                                    test_target_path = "tests/"
                                    if filepath_to_use and "test_" in Path(filepath_to_use).name.lower():
                                         test_target_path = filepath_to_use
                                         logger.info(f"Running tests specifically for target file: {test_target_path}")
                                    elif self.task_target_file and "test_" in Path(self.task_target_file).name.lower():
                                         resolved_task_target = self.context.get_full_path(self.task_target_file)
                                         if resolved_task_target:
                                             test_target_path = resolved_task_target
                                             logger.info(f"Running tests specifically for task target file: {test_target_path}")
                                         else:
                                             logger.warning(f"Task target file '{self.task_target_file}' looks like a test file but could not be resolved. Running all tests in 'tests/'.")
                                    else:
                                         logger.info(f"No specific test file identified for step or task. Running all tests in '{test_target_path}'.")

                                    test_command.append(test_target_path)

                                    try:
                                        return_code, stdout, stderr = self.execute_tests(test_command, self.context.base_path)
                                        test_results = self._parse_test_results(stdout)
                                        self._current_task_results['test_results'] = test_results
                                        self._current_task_results['test_stdout'] = stdout
                                        self._current_task_results['test_stderr'] = stderr
                                        self._current_task_results['last_test_command'] = test_command
                                        self._current_task_results['last_test_cwd'] = self.context.base_path

                                        logger.info(f"Test Execution Results: Status={test_results.get('status')}, Passed={test_results.get('passed')}, Failed={test_results.get('failed')}, Total={test_results.get('total')}")
                                        if test_results.get('status') == 'failed':
                                            logger.error(f"Tests failed for step: {step}. Raw stderr:\n{stderr}")
                                            raise RuntimeError("Tests failed for step.")
                                        elif test_results.get('status') == 'error':
                                            logger.error(f"Test execution or parsing error for step: {step}. Message: {test_results.get('message')}. Raw stderr:\n{stderr}")
                                            raise RuntimeError(f"Test execution or parsing error: {test_results.get('message')}")

                                    except Exception as e:
                                        logger.error(f"An unexpected error occurred during command execution or test parsing: {e}", exc_info=True)
                                        if 'test_results' not in self._current_task_results or self._current_task_results['test_results'].get('status') != 'error':
                                             self._current_task_results['test_results'] = {'status': 'error', 'passed': 0, 'failed': 0, 'total': 0, 'message': str(e)}
                                        raise e

                                elif prelim_flags['is_code_generation_step_prelim'] and filepath_to_use and filepath_to_use.endswith('.py'):
                                    logger.info(f"Step identified as code generation for file {filepath_to_use}. Orchestrating read-generate-merge-write.")
                                    existing_content = self._read_file_for_context(filepath_to_use)
                                    logger.debug(f"Read {len(existing_content)} characters from {filepath_to_use}.")
                                    context_for_llm = existing_content
                                    specific_instructions = (
                                        "Generate only the Python code snippet needed to fulfill the \"Specific Plan Step\". "
                                        "Do not include any surrounding text, explanations, or markdown code block fences (```). "
                                        "Provide just the raw code lines that need to be added or modified."
                                    )
                                    if self._is_add_imports_step(step):
                                        logger.info(f"Identified 'add imports' step. Optimizing context for {filepath_to_use}.")
                                        lines = existing_content.splitlines()
                                        import_block_end_line = self._find_import_block_end(lines)
                                        cutoff_line = min(import_block_end_line + 5, MAX_IMPORT_CONTEXT_LINES, len(lines))
                                        cutoff_line = max(0, cutoff_line)
                                        context_for_llm = "\n".join(lines[:cutoff_line])
                                        specific_instructions = (
                                            "You are adding import statements. Provide *only* the new import lines that need to be added. "
                                            "Do not repeat existing imports. Do not output any other code or explanation. "
                                            "Place the new imports appropriately within or after the existing import block."
                                        )
                                        logger.debug(f"Using truncated context for imports (up to line {cutoff_line}):\n{context_for_llm}")

                                    target_file_context_for_coder = ""
                                    target_file_context_for_coder = f"The primary file being modified for this step is specified as `{filepath_to_use}`. Focus your code generation on actions related to this file.\n\n"

                                    coder_prompt = f"""You are a Coder LLM expert in Python.
Your task is to generate only the code snippet required to implement the following specific step from a larger development plan.

Overall Task: "{next_task.get('task_name', 'Unknown Task')}"
Task Description: {next_task.get('description', 'No description provided.')}

{target_file_context_for_coder}
Specific Plan Step:
{step}

The primary file being modified is `{filepath_to_use}`.

EXISTING CONTENT OF `{filepath_to_use}`:
```python
{context_for_llm}
```
{specific_instructions}"""
                                    logger.debug("Invoking Coder LLM with prompt:\n%s", coder_prompt)
                                    generated_snippet = self._invoke_coder_llm(coder_prompt)

                                    if generated_snippet:
                                        logger.info(f"Coder LLM generated snippet (first 100 chars): {generated_snippet[:100]}...")
                                        logger.info(f"Performing pre-write validation for snippet targeting {filepath_to_use}...")
                                        validation_passed = True
                                        validation_feedback = []
                                        try:
                                            ast.parse(generated_snippet)
                                            logger.info("Pre-write syntax check (AST parse) passed for snippet.")
                                        except SyntaxError as se:
                                            validation_passed = False
                                            validation_feedback.append(f"Pre-write syntax check failed: {se}")
                                            logger.warning(f"Pre-write syntax validation (AST parse) failed for snippet: {se}")
                                            logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                        except Exception as e:
                                            validation_passed = False
                                            validation_feedback.append(f"Error during pre-write syntax validation (AST parse): {e}")
                                            logger.error(f"Error during pre-write syntax validation (AST parse): {e}", exc_info=True)
                                            logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")

                                        if validation_passed and self.default_policy_config:
                                            try:
                                                ethical_results = self.ethical_governance_engine.enforce_policy(generated_snippet, self.default_policy_config)
                                                if ethical_results.get('overall_status') == 'rejected':
                                                    validation_passed = False
                                                    validation_feedback.append(f"Pre-write ethical check failed: {ethical_results}")
                                                    logger.warning(f"Pre-write ethical validation failed for snippet: {ethical_results}")
                                                    logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                                else:
                                                    logger.info("Pre-write ethical validation passed for snippet.")
                                            except Exception as e:
                                                validation_passed = False
                                                validation_feedback.append(f"Error during pre-write ethical validation: {e}")
                                                logger.error(f"Error during pre-write ethical validation: {e}", exc_info=True)
                                                logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                        elif validation_passed:
                                            logger.warning("Skipping pre-write ethical validation: Default policy not loaded.")

                                        if validation_passed:
                                            try:
                                                style_review_results = self.code_review_agent.analyze_python(generated_snippet)
                                                critical_findings = [f for f in style_review_results.get('static_analysis', []) if f.get('severity') in ['error', 'security_high']]
                                                if critical_findings:
                                                    validation_passed = False
                                                    validation_feedback.append(f"Pre-write style/security check failed: Critical findings detected.")
                                                    logger.warning(f"Pre-write style/security validation failed for snippet. Critical findings: {critical_findings}")
                                                    logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")
                                                else:
                                                    logger.info("Pre-write style/security validation passed for snippet.")
                                            except Exception as e:
                                                validation_passed = False
                                                validation_feedback.append(f"Error during pre-write style/security validation: {e}")
                                                logger.error(f"Error during pre-write style/security validation: {e}", exc_info=True)
                                                logger.warning(f"Failed snippet:\n---\n{generated_snippet}\n---")

                                        if validation_passed:
                                            logger.info(f"Pre-write validation passed for snippet targeting {filepath_to_use}. Proceeding with merge/write.")
                                            merged_content = self._merge_snippet(existing_content, generated_snippet)
                                            logger.debug("Snippet merged.")
                                            logger.info(f"Attempting to write merged content to {filepath_to_use}.")
                                            try:
                                                self._write_output_file(filepath_to_use, merged_content, overwrite=True)
                                                logger.info(f"Successfully wrote merged content to {filepath_to_use}.")
                                                code_written_in_iteration = True
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

                                            except FileExistsError:
                                                logger.error(f"Unexpected FileExistsError when writing merged content to {filepath_to_use} with overwrite=True.")
                                                raise FileExistsError(f"Unexpected FileExistsError during write: {filepath_to_use}")
                                            except Exception as e:
                                                logger.error(f"Failed to write merged content to {filepath_to_use}: {e}", exc_info=True)
                                                raise e
                                        else:
                                            logger.warning(f"Pre-write validation failed for snippet targeting {filepath_to_use}. Skipping write/merge. Feedback: {validation_feedback}")
                                            raise ValueError(f"Pre-write validation failed for step {step_index + 1}.")
                                    else:
                                        logger.warning(f"Coder LLM returned empty or None snippet for step {step_index + 1}. Skipping file write.")
                                        raise ValueError(f"Coder LLM returned empty snippet for step {step_index + 1}.")

                                elif content_to_write is not None and filepath_to_use:
                                    logger.info(f"Step identified as explicit file writing. Processing file operation for step: {step}")
                                    logger.info(f"Attempting to write file: {filepath_to_use}.")
                                    try:
                                        self._write_output_file(filepath_to_use, content_to_write, overwrite=overwrite_mode)
                                        logger.info(f"Successfully wrote placeholder content to {filepath_to_use}.")
                                    except FileExistsError:
                                        logger.warning(f"File {filepath_to_use} already exists. Skipping write as overwrite={overwrite_mode}.")
                                    except Exception as e:
                                        logger.error(f"Failed to write file {filepath_to_use}: {e}", exc_info=True)
                                        raise e

                                else:
                                    logger.info(f"Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: {step}")

                                step_succeeded = True
                                break
                            except Exception as e:
                                logger.error(f"Error executing step {step_index + 1}/{len(solution_plan)} (Attempt {step_retries + 1}/{MAX_STEP_RETRIES + 1}): {step}", exc_info=True)
                                self._current_task_results['step_errors'].append({
                                    'step_index': step_index + 1,
                                    'step_description': step,
                                    'error_type': type(e).__name__,
                                    'error_message': str(e),
                                    'timestamp': datetime.utcnow().isoformat(),
                                    'attempt': step_retries + 1
                                })
                                step_retries += 1
                                if step_retries <= MAX_STEP_RETRIES:
                                    logger.warning(f"Step {step_index + 1} failed. Attempting retry {step_retries}/{MAX_STEP_RETRIES}...")
                                else:
                                    logger.error(f"Step {step_index + 1} failed after {MAX_STEP_RETRIES} retries.")
                                    task_failed_step = True
                                    break

                        if task_failed_step:
                            new_status = "Blocked"
                            last_error = next(
                                (err for err in reversed(self._current_task_results['step_errors'])
                                 if err['step_index'] == step_index + 1),
                                {"error_type": "UnknownError", "error_message": "No specific error logged."}
                            )
                            reason_blocked = f"Step {step_index + 1} ('{step}') failed after {MAX_STEP_RETRIES + 1} attempts. Last error: {last_error['error_type']}: {last_error['error_message']}"
                            logger.warning(f"Task {task_id} marked as '{new_status}'.")
                            self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                            break

                    if not task_failed_step:
                        logger.info("All plan steps executed successfully.")
                        logger.info("Generating Grade Report...")
                        grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                        logger.info(f"--- GRADE REPORT for Task {task_id} ---\n{grade_report_json}\n--- END GRADE REPORT ---")
                        evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                        recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                        justification = evaluation_result.get("justification", "Evaluation failed.")
                        logger.info(f"Initial Grade Report Evaluation: Recommended Action='{recommended_action}', Justification='{justification}'")

                        MAX_TASK_REMEDIATION_ATTEMPTS = 2
                        if recommended_action == "Regenerate Code":
                            if self.remediation_attempts < MAX_TASK_REMEDIATION_ATTEMPTS:
                                logger.info(f"Attempting automated remediation (Attempt {self.remediation_attempts + 1}/{MAX_TASK_REMEDIATION_ATTEMPTS})...")
                                self.remediation_occurred_in_pass = False

                                filepath_for_remediation = self.task_target_file
                                if not filepath_for_remediation:
                                    last_file_step_path = None
                                    for step_idx, plan_step_desc in reversed(list(enumerate(solution_plan))):
                                         prelim_flags_rem = self._classify_step_preliminary(plan_step_desc)
                                         step_filepath_rem = self._determine_filepath_to_use(plan_step_desc, self.task_target_file, prelim_flags_rem)
                                         if (prelim_flags_rem.get('is_code_generation_step_prelim') or prelim_flags_rem.get('is_explicit_file_writing_step_prelim')) and step_filepath_rem:
                                             last_file_step_path = step_filepath_rem
                                             break

                                    if last_file_step_path:
                                         filepath_for_remediation = last_file_step_path
                                         logger.debug(f"Using file path from last file step for remediation: {filepath_for_remediation}")

                                if not filepath_for_remediation:
                                    logger.error("No target file identified for remediation. Cannot attempt remediation.")
                                    new_status = "Blocked"
                                    reason_blocked = "Remediation recommended but no target file identified."
                                    logger.warning(f"Task {task_id} marked as '{new_status}'.")
                                    self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                                    continue
                                else:
                                    # Read the current content of the file for the remediation prompt
                                    # --- FIX: Resolve path before reading ---
                                    resolved_filepath_for_remediation_read = self.context.get_full_path(filepath_for_remediation)
                                    if resolved_filepath_for_remediation_read is None:
                                         logger.error(f"Failed to resolve file path for reading during remediation: {filepath_for_remediation}. Cannot attempt remediation.")
                                         new_status = "Blocked"
                                         reason_blocked = f"Remediation recommended but failed to resolve target file for reading: {filepath_for_remediation}"
                                         logger.warning(f"Task {task_id} marked as '{new_status}'.")
                                         self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                                         continue
                                    current_file_content = self._read_file_for_context(resolved_filepath_for_remediation_read)
                                    # --- END FIX ---

                                    if current_file_content is not None:
                                        failure_type = self._identify_remediation_target(grade_report_json)
                                        remediation_attempted = False
                                        remediation_success = False

                                        test_results = self._current_task_results.get('test_results', {})
                                        test_status = test_results.get('status')

                                        if test_status == 'failed':
                                             remediation_attempted = True
                                             # Pass the original relative file_path to the remediation method
                                             remediation_success = self._attempt_test_failure_remediation(
                                                 grade_report_json, next_task, "Test Failure Remediation", filepath_for_remediation, current_file_content
                                             )
                                             if remediation_success:
                                                 logger.info("Test failure remediation successful.")
                                                 self.remediation_occurred_in_pass = True
                                                 grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                                                 logger.info(f"--- REVISED GRADE REPORT (Test Remediation) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                                 evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                                 recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                                                 justification = evaluation_result.get("justification", "Evaluation failed.")
                                                 logger.info(f"Revised Grade Report Evaluation (Test Remediation): Recommended Action='{recommended_action}', Justification='{justification}'")
                                             else:
                                                 logger.warning("Test failure remediation attempt failed.")

                                        if not remediation_success and failure_type == "Code Style":
                                            remediation_attempted = True
                                            # Pass the original relative file_path to the remediation method
                                            remediation_success = self._attempt_code_style_remediation(grade_report_json, next_task, "Code Style Remediation", filepath_for_remediation, current_file_content)
                                            if remediation_success:
                                                logger.info("Style remediation attempt seems successful (code written).")
                                                self.remediation_occurred_in_pass = True
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
                                            # Pass the original relative file_path to the remediation method
                                            remediation_success = self._attempt_ethical_transparency_remediation(grade_report_json, next_task, "Ethical Transparency Remediation", filepath_for_remediation, current_file_content)
                                            if remediation_success:
                                                logger.info("Ethical transparency remediation seems successful (code written).")
                                                self.remediation_occurred_in_pass = True
                                                grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                                                logger.info(f"--- REVISED GRADE REPORT (Ethical) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                                evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                                recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                                                justification = evaluation_result.get("justification", "Evaluation failed.")
                                                logger.info(f"Revised Grade Report Evaluation (Ethical): Recommended Action='{recommended_action}', Justification='{justification}'")
                                            else:
                                                logger.warning("Ethical transparency remediation attempt failed.")

                                        if remediation_attempted and remediation_success:
                                            self.remediation_attempts += 1
                                            logger.info(f"Remediation attempt {self.remediation_attempts} completed.")
                                        elif remediation_attempted:
                                             logger.warning("Remediation attempt failed to write code.")
                                        else:
                                             logger.info("No applicable automated remediation identified or attempted.")

                                    else:
                                        logger.error(f"Failed to read current file content for remediation: {filepath_for_remediation}. Cannot attempt remediation.")
                                        new_status = "Blocked"
                                        reason_blocked = f"Remediation recommended but failed to read target file: {filepath_for_remediation}"
                                        logger.warning(f"Task {task_id} marked as '{new_status}'.")
                                        self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                                        continue

                            else:
                                logger.warning(f"Maximum task-level remediation attempts ({MAX_TASK_REMEDIATION_ATTEMPTS}) reached for task {task_id}. Proceeding without further automated remediation.")

                        new_status = next_task['status']
                        reason_blocked = None

                        if recommended_action == "Completed":
                            new_status = "Completed"
                        elif recommended_action == "Blocked":
                            new_status = "Blocked"
                            reason_blocked = justification

                        if new_status != next_task['status']:
                            logger.info(f"Updating task status from '{next_task['status']}' to '{new_status}' for task {task_id}")
                            self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
                        else:
                            logger.info(f"Task status for {task_id} remains '{new_status}' based on evaluation.")

                else:
                    logger.warning(f"No solution plan generated for task {task_id}.")
                    logger.info(f"Task {task_id} requires manual review due to failed plan generation.")
                    new_status = "Blocked"
                    reason_blocked = "Failed to generate a solution plan."
                    logger.warning(f"Task {task_id} marked as '{new_status}'.")
                    self._update_task_status_in_roadmap(task_id, new_status, reason_blocked)
            else:
                logger.info('No tasks available in Not Started status. Exiting autonomous loop.')
                break
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
        # This method expects a full path already resolved by the caller
        if not isinstance(full_file_path, str) or full_file_path == "":
            logger.warning(f"Attempted to read file with invalid full path: {full_file_path}")
            return ""
        # No need to resolve again, assume it's already resolved and validated
        full_path = full_file_path
        if not os.path.exists(full_path):
            logger.warning(f"File not found for reading: {full_path}")
            return ""
        if not os.path.isfile(full_path):
            logger.warning(f"Path is not a file: {full_path}")
            return ""
        try:
            file_size = os.path.getsize(full_path)
            if file_size > MAX_READ_FILE_SIZE:
                logger.warning(f"File exceeds maximum read size ({MAX_READ_FILE_SIZE} bytes): {full_path} ({file_size} bytes)")
                return ""
        except Exception as e:
            logger.error(f"Error checking file size for {full_path}: {e}", exc_info=True)
            return ""
        try:
            with builtins.open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            logger.debug(f"Successfully read {len(content)} characters from {full_path}")
            return content
        except PermissionError:
            logger.error(f"Permission denied when reading file: {full_path}")
            return ""
        except Exception as e:
            logger.error(f"Unexpected error reading file {full_path}: {e}", exc_info=True)
            return ""

    def generate_solution_plan(self, task: dict) -> list[str]:
        if not isinstance(task, dict) or 'task_name' not in task or 'description' not in task:
            logger.error("Invalid task dictionary provided for plan generation.")
            return []
        task_name = task['task_name']
        description = task['description']
        target_file_context = ""
        task_target_file = task.get('target_file')
        if task_target_file:
            target_file_context = f"The primary file being modified for this task is specified as `{task_target_file}` in the task metadata. Focus your plan steps on actions related to this file.\n\n"
        planning_prompt = f"""You are an AI assistant specializing in software development workflows.
Your task is to generate a step-by-step solution plan for the following development task from the Metamorphic Software Genesis Ecosystem roadmap.
Please provide the plan as a numbered markdown list. Do not include any introductory or concluding remarks outside the list.

Task Name: {task_name}

Task Description:
{description}

{target_file_context}When generating steps that involve modifying the primary file for this task, ensure you refer to the file identified in the context (e.g., src/core/automation/workflow_driver.py).
"""
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
        if not re.fullmatch(r'^[a-zA-Z0-9_-]+(?:\.[a-zA-Z0-9_-]+)*$', filename):
             if not re.fullmatch(r'^[a-zA-Z0-9_-]+$', filename):
                 return False
        return True

    def _write_output_file(self, full_filepath: str, content: str, overwrite: bool = False) -> bool:
        # This method expects a full path already resolved and validated by the caller
        if not isinstance(full_filepath, str) or full_filepath == "":
            logger.error(f"_write_output_file received invalid full filepath: {full_filepath}")
            return False
        try:
            resolved_filepath = Path(full_filepath)
        except Exception as e:
            logger.error(f"Error creating Path object for full filepath {full_filepath} for writing: {e}", exc_info=True)
            return False

        parent_dir = resolved_filepath.parent
        if not parent_dir.exists():
            try:
                parent_dir.mkdir(parents=True, exist_ok=True)
                logger.info(f"Created directory: {parent_dir}")
            except Exception as e:
                logger.error(f"Failed to create directory {parent_dir}: {e}", exc_info=True)
                return False
        try:
            result = write_file(str(resolved_filepath), content, overwrite=overwrite)
            return result
        except FileExistsError as e:
            if not overwrite:
                 raise e
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
            error_msg = f"Error: Command executable '{test_command[0]}' not found or working directory '{cwd}' does not exist. Ensure '{test_command[0]}' is in your system's PATH and the working directory is valid."
            stderr = error_msg
            return_code = 127
            logger.error(error_msg)
        except Exception as e:
            error_msg = f"An unexpected error occurred during command execution: {e}"
            stderr = error_msg
            return_code = 1
            logger.error(error_msg)
        self._current_task_results['test_stdout'] = stdout
        self._current_task_results['test_stderr'] = stderr
        self._current_task_results['last_test_command'] = test_command
        self._current_task_results['last_test_cwd'] = cwd
        return return_code, stdout, stderr

    def _merge_snippet(self, existing_content: str, snippet: str) -> str:
        if not snippet:
            return existing_content
        marker_index = existing_content.find(METAMORPHIC_INSERT_POINT)
        if marker_index != -1:
            return existing_content.replace(METAMORPHIC_INSERT_POINT, snippet, 1)
        else:
            if existing_content and not existing_content.endswith('\n'):
                return existing_content + "\n" + snippet
            return existing_content + snippet

    def _parse_test_results(self, raw_output: str) -> dict:
        if not raw_output:
            logger.warning("Received empty output for test results parsing.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Received empty output.'}
        summary_lines = [line for line in raw_output.splitlines() if line.strip().startswith('==') and ('test session' in line or 'passed' in line or 'failed' in line or 'skipped' in line or 'error' in line)]
        if not summary_lines:
            logger.warning("Could not find pytest summary lines in output.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not find pytest summary lines in output.'}

        final_summary_line = summary_lines[-1]

        counts_pattern = re.compile(r'(\d+) (passed|failed|skipped|error)')
        matches = counts_pattern.findall(final_summary_line)

        passed = 0
        failed = 0
        skipped = 0
        errors = 0
        total = 0

        for count_str, status_str in matches:
            try:
                count = int(count_str)
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
                return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not parse test results output.'}

        if failed > 0 or errors > 0:
            status = 'failed'
        elif total > 0:
            status = 'passed'
        else:
            status = 'error'
            logger.warning(f"No test results counts found or total is zero. Summary line: {final_summary_line}")
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

    def generate_grade_report(self, task_id: str, validation_results: dict) -> str:
        report = {
            "task_id": task_id,
            "timestamp": datetime.utcnow().isoformat(),
            "validation_results": {
                "tests": validation_results.get('test_results', {}),
                "code_review": validation_results.get('code_review_results', {}),
                "ethical_analysis": validation_results.get('ethical_analysis_results', {}),
                "step_errors": validation_results.get('step_errors', [])
            },
            "grades": self._calculate_grades(validation_results)
        }
        return json.dumps(report, indent=2)

    def _calculate_grades(self, validation_results: dict) -> dict:
        grades = {
            "non_regression": {"percentage": 0, "justification": "No non-regression tests executed."},
            "test_success": {"percentage": 0, "justification": "No test results available."},
            "code_style": {"percentage": 0, "justification": "No code review results available."},
            "ethical_policy": {"percentage": 0, "justification": "No ethical analysis results available."},
            "security_soundness": {"percentage": 0, "justification": "No security results available."}
        }

        test_results = validation_results.get('tests')
        if test_results and test_results.get('status') != 'error':
            total_tests = test_results.get('total', 0)
            passed_tests = test_results.get('passed', 0)
            if total_tests > 0:
                percentage = 100 * (passed_tests / total_tests)
                grades['test_success'] = {
                    "percentage": round(percentage),
                    "justification": f"Tests executed: {total_tests}, Passed: {passed_tests}, Failed: {test_results.get('failed', 0)}, Status: {test_results.get('status')}"
                }
            elif test_results.get('status') == 'passed':
                 grades['test_success'] = {
                    "percentage": 100,
                    "justification": f"Test status is 'passed' with 0 total tests (e.g., no tests collected)."
                }
            else:
                 grades['test_success'] = {
                    "percentage": 0,
                    "justification": f"Test status is '{test_results.get('status')}' with 0 total tests."
                }
        elif test_results and test_results.get('status') == 'error':
            grades['test_success'] = {
                "percentage": 0,
                "justification": f"Test execution or parsing error: {test_results.get('message', 'Unknown error')}"
            }

        code_review_results = validation_results.get('code_review')
        if code_review_results and code_review_results.get('status') != 'error':
            all_findings = code_review_results.get('static_analysis', [])
            code_style_findings = [f for f in all_findings if not f.get('severity', '').startswith('security')]
            security_findings = [f for f in all_findings if f.get('severity', '').startswith('security')]

            high_style_issues = [f for f in code_style_findings if f.get('severity') in ['error', 'warning']]
            other_style_issues = [f for f in code_style_findings if f.get('severity') not in ['error', 'warning']]
            style_high_penalty = 15
            style_other_penalty = 3
            calculated_style_percentage = 100 - (len(high_style_issues) * style_high_penalty + len(other_style_issues) * style_other_penalty)
            style_percentage = max(0, calculated_style_percentage)
            grades['code_style'] = {
                "percentage": style_percentage,
                "justification": f"Code review found {len(code_style_findings)} style issues ({len(high_style_issues)} high severity style). Status: {code_review_results.get('status')}"
            }

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
                "justification": f"Security scan found {len(security_findings)} security findings ({len(high_security_findings)} high, {len(medium_security_findings)} medium, {len(low_security_findings)} low)."
            }
        elif code_review_results and code_review_results.get('status') == 'error':
            error_justification = f"Code review/security execution error: {code_review_results.get('errors', {}).get('flake8', 'N/A')}, {code_review_results.get('errors', {}).get('bandit', 'N/A')}"
            grades['code_style'] = {"percentage": 0, "justification": error_justification}
            grades['security_soundness'] = {"percentage": 0, "justification": error_justification}

        grades['non_regression'] = {
            "percentage": 100 if grades['test_success']['percentage'] == 100 else 0,
            "justification": "Non-regression testing is a placeholder. Graded based on Test Success (100% if tests passed, 0% otherwise)."
        }

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
        justification = "Default action based on unhandled scenario."

        if step_errors:
             recommended_action = "Manual Review Required"
             justification = f"Step execution errors occurred ({len(step_errors)} errors). Manual review required."
             logger.warning(f"Step execution errors detected. Recommended Action: {recommended_action}")
             return {"recommended_action": recommended_action, "justification": justification}

        if ethical_analysis_results.get('overall_status') == 'rejected':
            recommended_action = "Blocked"
            justification = "Ethical analysis rejected the code."
        elif code_review_results.get('static_analysis') and any(f.get('severity') == 'security_high' for f in code_review_results['static_analysis']):
            recommended_action = "Blocked"
            justification = "High-risk security findings detected."
        elif test_results.get('status') == 'failed':
            recommended_action = "Regenerate Code"
            justification = "Automated tests failed."
        elif test_results.get('status') == 'error':
             recommended_action = "Regenerate Code"
             justification = f"Test execution or parsing error: {test_results.get('message', 'Unknown error')}."
        elif code_review_results.get('status') == 'error':
             recommended_action = "Regenerate Code"
             justification = f"Code review or security scan execution error."
        elif ethical_analysis_results.get('overall_status') == 'error':
             recommended_action = "Regenerate Code"
             justification = f"Ethical analysis execution error: {ethical_analysis_results.get('message', 'Unknown error')}."
        elif overall_percentage_grade == 100:
            recommended_action = "Completed"
            justification = "Overall grade is 100%."
        elif overall_percentage_grade >= 80:
            recommended_action = "Regenerate Code"
            justification = f"Overall grade ({overall_percentage_grade}%) is below 100% but meets regeneration threshold."
        else:
            recommended_action = "Manual Review Required"
            justification = f"Overall grade ({overall_percentage_grade}%) is below regeneration threshold or other issues require manual review."

        logger.info(f"Recommended Action: {recommended_action}. Justification: {justification}")
        return {"recommended_action": recommended_action, "justification": justification}

    def _safe_write_roadmap_json(self, roadmap_path: str, new_content: dict) -> bool:
        resolved_filepath = self.context.get_full_path(roadmap_path)
        if resolved_filepath is None:
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
        temp_filename = f".{resolved_filepath_obj.name}.{uuid.uuid4()}.tmp"
        temp_filepath = roadmap_dir / temp_filename

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

            os.replace(temp_filepath, resolved_filepath)

            logger.info(f"Successfully wrote updated roadmap to {roadmap_path}")
            return True

        except (IOError, OSError, PermissionError, json.JSONDecodeError) as e:
            logger.error(f"Error writing roadmap file {roadmap_path}: {e}", exc_info=True)
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after error: {e}")
                except Exception as cleanup_e_inner:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after error: {cleanup_e_inner}")
            return False
        except Exception as cleanup_e:
            logger.error(f"Unexpected error during roadmap file write {roadmap_path}: {cleanup_e}", exc_info=True)
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after unexpected error: {cleanup_e}")
                except Exception as cleanup_e_inner:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after unexpected error: {cleanup_e_inner}")
            return False

    def _update_task_status_in_roadmap(self, task_id: str, new_status: str, reason: str = None):
        try:
            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
            if full_roadmap_path is None:
                logger.error(f"Cannot update roadmap status: Invalid roadmap path provided: {self.roadmap_path}")
                return

            try:
                # Use builtins.open explicitly
                with builtins.open(full_roadmap_path, 'r') as f:
                    roadmap_data = json.load(f)
            except FileNotFoundError:
                logger.error(f"Error updating roadmap status for task {task_id}: Roadmap file not found at {full_roadmap_path}")
                return
            except json.JSONDecodeError:
                logger.error(f"Error updating roadmap status for task {task_id}: Invalid JSON in roadmap file {full_roadmap_path}")
                return
            except Exception as e:
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
                if self._safe_write_roadmap_json(self.roadmap_path, roadmap_data):
                    logger.info(f"Successfully wrote updated status for task {task_id} in {self.roadmap_path}")
                else:
                    logger.error(f"Failed to safely write updated roadmap for task {task_id}")
            else:
                logger.warning(f"Task {task_id} not found in roadmap file {self.roadmap_path} for status update.")

        except Exception as e:
            logger.error(f"Error updating roadmap status for task {task_id}: {e}", exc_info=True)

    def _identify_remediation_target(self, grade_report_json: str) -> str | None:
        try:
            report_data = json.loads(grade_report_json)
            grades = report_data.get('grades', {})
            validation = report_data.get('validation_results', {})

            test_results = validation.get('tests', {})
            if test_results.get('status') == 'failed':
                 logger.debug("Identified Test Failure as remediation target.")
                 return "Test Failure"

            ethical_results = validation.get('ethical_analysis', {})
            if ethical_results.get('overall_status') == 'rejected':
                if ethical_results.get('TransparencyScore', {}).get('status') == 'violation':
                    logger.debug("Identified Ethical Transparency as remediation target.")
                    return "Ethical Transparency"
                else:
                    logger.debug("Ethical rejection not due to TransparencyScore, no specific ethical remediation target identified.")

            code_style_grade = grades.get('code_style', {}).get('percentage', 100)
            code_review_results = validation.get('code_review', {})
            if code_style_grade < 100 and code_review_results.get('static_analysis'):
                style_findings = [f for f in code_review_results.get('static_analysis', []) if not f.get('severity', '').startswith('security')]
                if style_findings:
                    logger.debug("Identified Code Style as remediation target.")
                    return "Code Style"
                else:
                    logger.debug("Code style grade below 100, but no non-security static analysis findings found.")
            elif code_style_grade < 100:
                 logger.debug("Code style grade below 100, but code review results or static analysis findings are missing.")

            logger.debug("No specific remediation target identified from grade report for automated remediation.")
            return None

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for remediation target identification.")
            return None
        except Exception as e:
            logger.error(f"Error identifying remediation target: {e}", exc_info=True)
            return None

    def _attempt_code_style_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        logger.info(f"Attempting code style remediation for {file_path}...")
        try:
            report_data = json.loads(grade_report_json)
            code_review_results = report_data.get('validation_results', {}).get('code_review', {})
            findings = code_review_results.get('static_analysis', [])
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
```python
{original_code}
```

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

            # Resolve file_path before writing
            resolved_file_path = self.context.get_full_path(file_path)
            if resolved_file_path is None:
                logger.error(f"Failed to resolve file path for code style remediation: {file_path}. Aborting remediation.")
                return False

            write_success = self._write_output_file(resolved_file_path, content_to_write, overwrite=True)

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

                return True
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.")
                return False

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for code style remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during code style remediation: {e}", exc_info=True)
            return False

    def _attempt_ethical_transparency_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
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
```python
{original_code}
```

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

            # Resolve file_path before writing
            resolved_file_path = self.context.get_full_path(file_path)
            if resolved_file_path is None:
                logger.error(f"Failed to resolve file path for ethical transparency remediation: {file_path}. Aborting remediation.")
                return False

            write_success = self._write_output_file(resolved_file_path, content_to_write, overwrite=True)

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

                return True
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.")
                return False

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for ethical transparency remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during ethical transparency remediation: {e}", exc_info=True)
            return False

    def _attempt_test_failure_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        logger.info(f"Attempting test failure remediation for {file_path}...")
        try:
            stdout = self._current_task_results.get('test_stdout', '')
            stderr = self._current_task_results.get('test_stderr', '')
            test_results = self._current_task_results.get('test_results', {})

            if test_results.get('status') != 'failed':
                logger.warning("Test failure remediation triggered, but test status is not 'failed'.")
                return False

            logger.debug(f"Test failure details - Stdout: {stdout}, Stderr: {stderr}")

            # Read the current file content again, in case it was modified by other steps
            resolved_file_path_read = self.context.get_full_path(file_path)
            if resolved_file_path_read is None:
                 logger.error(f"Failed to resolve file path for reading during test remediation: {file_path}. Cannot attempt remediation.")
                 return False
            current_file_content = self._read_file_for_context(resolved_file_path_read)

            if not current_file_content or resolved_file_path_read is None: # Check resolved_file_path_read instead of file_path
                logger.error(f"Failed to read current file content for {file_path} during test remediation. Cannot attempt remediation.")
                return False

            task_name = task.get('task_name', 'Unknown Task')
            task_description = task.get('description', 'No description provided')

            prompt = f"""
You are tasked with fixing the following test failure in the Python code.
Task: {task_name}
Description: {task_description}
File to modify: {file_path}

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
Generate the complete, corrected Python code for the file {file_path}. Your response should contain the entire content of the file after applying the necessary fixes.
Do NOT include any surrounding text, explanations, or markdown code block fences (```). Provide just the raw code lines that constitute the complete, corrected file content.
Maintain all original logic and functionality not related to the test failures.
Adhere to PEP 8 style guidelines.
Note: The Debug Agent (task_2_2_6) is NOT available; you must generate the fix directly based on the provided information.
Your response should be the complete, corrected code content that addresses the test failure based on the provided context and error messages.
"""
            logger.debug("Invoking Coder LLM for test failure remediation...")
            corrected_code = self._invoke_coder_llm(prompt)

            if not corrected_code or corrected_code.strip() == current_file_content.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged for test failure remediation.")
                return False

            logger.info("LLM provided corrected code for test failure. Applying and re-validating...")
            content_to_write = corrected_code

            # Resolve file_path before writing
            resolved_file_path_write = self.context.get_full_path(file_path)
            if resolved_file_path_write is None:
                 logger.error(f"Failed to resolve file path for writing during test remediation: {file_path}. Aborting remediation.")
                 return False

            write_success = self._write_output_file(resolved_file_path_write, content_to_write, overwrite=True)

            if write_success:
                logger.info(f"Successfully wrote fixed code to {file_path}")
                try:
                    logger.info(f"Re-running validations for {file_path} after test failure remediation...")
                    test_command = self._current_task_results.get('last_test_command', ['pytest', 'tests/'])
                    cwd = self._current_task_results.get('last_test_cwd', self.context.base_path)
                    return_code, new_stdout, new_stderr = self.execute_tests(test_command, cwd)
                    self._current_task_results['test_stdout'] = new_stdout
                    self._current_task_results['test_stderr'] = new_stderr
                    self._current_task_results['test_results'] = self._parse_test_results(new_stdout)

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
                    if 'test_results' not in self._current_task_results or self._current_task_results['test_results'].get('status') != 'error':
                         self._current_task_results['test_results'] = {'status': 'error', 'passed': 0, 'failed': 0, 'total': 0, 'message': f"Re-validation error: {e}"}
                    if 'code_review_results' not in self._current_task_results or self._current_task_results['code_review_results'].get('status') != 'error':
                         self._current_task_results['code_review_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                    if 'ethical_analysis_results' not in self._current_task_results or self._current_task_results['ethical_analysis_results'].get('overall_status') != 'error':
                         self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': f"Re-validation error: {e}"}

                return True
            else:
                logger.error(f"Failed to write fixed code to {file_path}. Aborting test failure remediation.")
                return False

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for test failure remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during test failure remediation: {e}", exc_info=True)
            return False