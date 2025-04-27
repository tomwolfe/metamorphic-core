# src/core/automation/workflow_driver.py
import logging
import html
import os
import json
from pathlib import Path
from src.core.llm_orchestration import EnhancedLLMOrchestrator
import re
from unittest.mock import MagicMock
from src.cli.write_file import write_file  # Ensure write_file is imported
import subprocess # Import subprocess for execute_tests
from src.core.agents.code_review_agent import CodeReviewAgent # Import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine # Import EthicalGovernanceEngine
from datetime import datetime # Import datetime for report timestamp

logger = logging.getLogger(__name__)

# Define a maximum file size for reading (e.g., 1MB)
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"


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

        if not isinstance(relative_path, str) or not relative_path: # Added check for empty string
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
        self.tasks = []  # Will be loaded by start_workflow
        self._current_task_results = {} # Dictionary to store results for the current task iteration # ADDED

        # Initialize LLM Orchestrator - Pass placeholder dependencies for now
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=MagicMock(),
            ethics_engine=MagicMock()
        )
        # Instantiate CodeReviewAgent
        self.code_review_agent = CodeReviewAgent()

        # Instantiate EthicalGovernanceEngine and load default policy # ADDED BLOCK
        self.ethical_governance_engine = EthicalGovernanceEngine()
        self._load_default_policy() # Extract policy loading to a separate method
        # END ADDED BLOCK

    def _load_default_policy(self):
        """Load the default ethical policy from file."""
        # Use context.get_full_path for safety when loading the policy file
        default_policy_path = self.context.get_full_path("policies/policy_bias_risk_strict.json")
        if default_policy_path:
            try:
                self.default_policy_config = self.ethical_governance_engine.load_policy_from_json(default_policy_path)
                logger.info(f"Loaded default ethical policy: {self.default_policy_config.get('policy_name')}")
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
            return # Exit if roadmap loading fails
        self.context = context  # Update context if needed (though it's set in __init__)
        logger.info(f"Workflow initiated with roadmap: {roadmap_path}, output: {output_dir}")
        self.autonomous_loop()

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

        while True:
            logger.info('Starting autonomous loop iteration')
            self._current_task_results = {} # Reset results for the new task iteration # ADDED

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

                solution_plan = self.generate_solution_plan(next_task)
                logger.info(f'Generated plan: {solution_plan}')

                if solution_plan:
                    logger.info(
                        f"Executing plan for task {task_id} with {len(solution_plan)} steps.")
                    for step_index, step in enumerate(solution_plan):
                        logger.info(f"Executing step {step_index + 1}/{len(solution_plan)}: {step}")

                        step_lower = step.lower()  # Convert step to lower once
                        code_generation_keywords = ["implement", "generate code",
                                                    "write function", "modify file",
                                                    "add logic to"]
                        file_writing_keywords = ["write file", "create file", "save to file",
                                                 "output file", "generate file"]
                        test_execution_keywords = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]

                        # Determine the actual filepath to use: prioritize target_file from task
                        task_target_file = next_task.get('target_file')
                        # Fallback: Check for a file path match using the regex
                        filepath_match = re.search(
                            r'(\S+\.(py|md|json|txt|yml|yaml))', step, re.IGNORECASE)
                        filepath_from_step = filepath_match.group(1) if filepath_match else None
                        filepath_to_use = task_target_file if task_target_file else filepath_from_step

                        is_file_writing_step = (filepath_to_use is not None) or any(
                            keyword in step_lower for keyword in file_writing_keywords)

                        needs_coder_llm = any(
                            keyword in step_lower for keyword in code_generation_keywords)

                        is_test_execution_step = any(keyword in step_lower for keyword in test_execution_keywords)

                        generated_output = None  # Initialize generated_output for this step
                        content_to_write = None # Initialize content_to_write
                        overwrite_file = False # Initialize overwrite flag

                        # --- START MODIFIED LOGIC FOR STEP PROCESSING (REORDERED) ---
                        # Prioritize test execution steps
                        if is_test_execution_step:
                             logger.info(f"Step identified as test execution. Running tests for step: {step}")
                             # Determine test command - This is a simplification for Phase 1.6
                             # A more sophisticated approach would infer the target test file from the previous steps or task metadata
                             # For now, if a target_file is specified and looks like a test file, use it. Otherwise, default.
                             test_command = ["pytest"]
                             # FIX: Simplify test command heuristic - use filepath_to_use if available
                             if filepath_to_use:
                                 test_command.append(filepath_to_use)
                             else:
                                 test_command.append("tests/") # Default to running all tests in tests/


                             # Execute tests
                             return_code, stdout, stderr = self.execute_tests(test_command, self.context.base_path)

                             # Parse test results
                             test_results = self._parse_test_results(stdout)
                             self._current_task_results['test_results'] = test_results # Store test results # ADDED

                             # Log parsed results
                             logger.info(f"Test Execution Results: Status={test_results['status']}, Passed={test_results['passed']}, Failed={test_results['failed']}, Total={test_results['total']}")
                             if test_results['status'] == 'failed':
                                 logger.error(f"Tests failed for step: {step}. Raw stderr:\n{stderr}")
                             elif test_results['status'] == 'error':
                                 logger.error(f"Test execution or parsing error for step: {step}. Message: {test_results['message']}. Raw stderr:\n{stderr}")

                        # Prioritize code generation steps targeting a specific file
                        elif needs_coder_llm and filepath_to_use:
                            logger.info(
                                f"Step identified as code generation for file {filepath_to_use}. Orchestrating read-generate-merge-write.")

                            # 1. Read existing content
                            existing_content = self._read_file_for_context(filepath_to_use)
                            logger.debug(f"Read {len(existing_content)} characters from {filepath_to_use}.")

                            # 2. Construct prompt and invoke Coder LLM for snippet
                            coder_prompt = f"""You are a Coder LLM expert in Python.
Your task is to generate *only the code snippet* required to implement the following specific step from a larger development plan.

Overall Task: "{next_task.get('task_name', 'Unknown Task')}"
Task Description: {next_task.get('description', 'No description provided.')}

Specific Plan Step:
{step}

The primary file being modified is `{filepath_to_use}`.

EXISTING CONTENT OF `{filepath_to_use}`:
```python
{existing_content}
```

Generate *only* the Python code snippet needed to fulfill the "Specific Plan Step". Do not include any surrounding text, explanations, or markdown code block fences (```). Provide just the raw code lines that need to be added or modified.
"""
                            logger.debug("Invoking Coder LLM with prompt: %s", coder_prompt[:500])
                            generated_snippet = self._invoke_coder_llm(coder_prompt)

                            if generated_snippet:
                                logger.info(
                                    f"Coder LLM generated snippet (first 100 chars): {generated_snippet[:100]}...")

                                # 3. Merge snippet into existing content
                                merged_content = self._merge_snippet(existing_content, generated_snippet)
                                logger.debug("Snippet merged.")

                                # 4. Write merged content back to file (overwrite=True)
                                logger.info(f"Attempting to write merged content to {filepath_to_use}.")
                                try:
                                    self._write_output_file(filepath_to_use, merged_content, overwrite=True)
                                    logger.info(f"Successfully wrote merged content to {filepath_to_use}.")

                                    # --- ADDED: Call CodeReviewAgent and Ethical Analysis after successful write ---
                                    try:
                                        logger.info(f"Running code review and security scan for {filepath_to_use}...")
                                        review_results = self.code_review_agent.analyze_python(merged_content)
                                        self._current_task_results['code_review_results'] = review_results # Store code review/security results # ADDED
                                        logger.info(f"Code Review and Security Scan Results for {filepath_to_use}: {review_results}")
                                    except Exception as review_e:
                                        logger.error(f"Error running code review/security scan for {filepath_to_use}: {review_e}", exc_info=True)
                                        self._current_task_results['code_review_results'] = {'status': 'error', 'message': str(review_e)} # Store error

                                    if self.default_policy_config:
                                        try:
                                            logger.info(f"Running ethical analysis for {filepath_to_use}...")
                                            ethical_analysis_results = self.ethical_governance_engine.enforce_policy(merged_content, self.default_policy_config)
                                            self._current_task_results['ethical_analysis_results'] = ethical_analysis_results # Store ethical analysis results # ADDED
                                            logger.info(f"Ethical Analysis Results for {filepath_to_use}: {ethical_analysis_results}")
                                        except Exception as ethical_e:
                                            logger.error(f"Error running ethical analysis for {filepath_to_use}: {ethical_e}", exc_info=True)
                                            self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': str(ethical_e)} # Store error
                                    else:
                                        logger.warning("Default ethical policy not loaded. Skipping ethical analysis.")
                                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded.'} # Indicate skipped
                                    # --- END ADDED BLOCK ---


                                except FileExistsError:
                                    # This should not happen with overwrite=True, but handle defensively
                                    logger.error(f"Unexpected FileExistsError when writing merged content to {filepath_to_use} with overwrite=True.")
                                except Exception as e:
                                    logger.error(f"Failed to write merged content to {filepath_to_use}: {e}", exc_info=True)
                            else:
                                logger.warning(f"Coder LLM returned empty or None snippet for step {step_index + 1}. Skipping file write.")

                        # Handle steps identified as file writing, but NOT code generation (e.g., writing a report)
                        elif is_file_writing_step and not needs_coder_llm and filepath_to_use:
                             logger.info(f"Step identified as file writing (non-code-gen). Processing file operation for step: {step}")
                             # For now, use placeholder content. In future tasks, this would involve
                             # invoking a different agent or logic to generate the file content.
                             content_to_write = f"// Placeholder content for step: {step}"
                             logger.info(f"Using placeholder content for file: {filepath_to_use}")
                             logger.info(f"Attempting to write file: {filepath_to_use}")
                             try:
                                 # Use overwrite=False as a default for non-code-gen writes,
                                 # unless the step explicitly indicates overwrite.
                                 # This logic might need refinement in future tasks.
                                 self._write_output_file(filepath_to_use, content_to_write, overwrite=False)
                             except FileExistsError:
                                 logger.warning(
                                     f"File {filepath_to_use} already exists. Skipping write as overwrite=False.")
                             except Exception as e:
                                 logger.error(f"Failed to write file {filepath_to_use}: {e}",
                                              exc_info=True)

                        # Handle steps identified as file writing or code generation, but without a determined filepath
                        elif (is_file_writing_step or needs_coder_llm) and not filepath_to_use:
                             logger.warning(
                                 f"Step identified as file operation or code generation but could not determine filepath for step '{step}'. Skipping file operation.")

                        # Log if the step was not identified as involving file operations, code generation, or test execution
                        else: # not needs_coder_llm and not is_file_writing_step and not is_test_execution_step
                            logger.info(
                                f"Step not identified as code generation, file writing, or test execution. Skipping agent invocation/file write for step: {step}")
                        # --- END MODIFIED LOGIC FOR STEP PROCESSING ---

                    # --- ADDED: Generate and Log Grade Report after all steps for the task ---
                    logger.info("Generating Grade Report...")
                    # Ensure task_id is available here (it's available from the selected_task dict)
                    task_id = next_task.get('task_id', 'Unknown ID') # Get task_id from the task dict
                    grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                    logger.info(f"--- GRADE REPORT for Task {task_id} ---\n{grade_report_json}\n--- END GRADE REPORT ---")
                    # END ADDED BLOCK


                else: # This 'else' corresponds to 'if solution_plan:'
                    logger.warning(f"No solution plan generated for task {task_id}.")

            else: # This 'else' corresponds to 'if next_task:'
                logger.info('No tasks available in Not Started status. Exiting autonomous loop.')
                break # This break exits the while True loop

        logger.info('Autonomous loop terminated.')

    def _read_file_for_context(self, relative_file_path: str) -> str:
        """
        Reads content from a file, handling errors and size limits.

        Args:
            relative_file_path: The path to the file, relative to the context's base_path.

        Returns:
            The content of the file as a string, or an empty string if reading fails
            or the file exceeds the size limit.
        """
        if not isinstance(relative_file_path, str) or not relative_file_path:
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
            with open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
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

        # --- ADDED CONTEXT ABOUT THE TARGET FILE ---
        # This is a heuristic based on the task name/description.
        # A more robust system might infer this from the Knowledge Graph or task metadata.
        target_file_context = ""
        task_target_file = task.get('target_file')
        if task_target_file:
             target_file_context = f"The primary file being modified for this task is specified as `{task_target_file}` in the task metadata. Focus your plan steps on actions related to this file."
        elif "WorkflowDriver" in task_name or "workflow_driver.py" in description:
             target_file_context = "The primary file being modified for this task is `src/core/automation/workflow_driver.py`."
        # Add more heuristics here for other common files if needed
        # --- END ADDED BLOCK ---

        planning_prompt = f"""You are an AI assistant specializing in software development workflows.
Your task is to generate a step-by-step solution plan for the following development task from the Metamorphic Software Genesis Ecosystem roadmap.

Task Name: {task_name}

Task Description:
{description}

{target_file_context}

Please provide the plan as a numbered markdown list. Do not include any introductory or concluding remarks outside the list.
When generating steps that involve modifying the primary file for this task, ensure you refer to the file identified in the context (e.g., `src/core/automation/workflow_driver.py`).
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
        """Selects the next task with status 'Not Started' from the list.

        Args:
            tasks: A list of task dictionaries. Each task must contain a 'status' key.

        Returns:
            The first task dictionary with a status of 'Not Started', or None if no such task exists or the list is empty.
        """
        if not isinstance(tasks, list):
            logger.warning(f"select_next_task received non-list input: {type(tasks)}")
            return None

        for task in tasks:
            if isinstance(task, dict) and 'status' in task and 'task_id' in task:
                task_id = task.get('task_id')
                if task['status'] == 'Not Started':
                    if task_id and self._is_valid_task_id(task_id):
                        return task
                    elif task_id:
                        logger.warning(f"Skipping task with invalid task_id format: {task_id}")
            else:
                logger.warning(f"Skipping invalid task format in list: {task}")

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
- Follow best practices for code quality and style.
- Prioritize security, and prevent code injection vulnerabilities.
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
            markdown_steps += f"{i + 1}.  - [ ] {html.escape(step)}\n"
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
            with open(full_roadmap_path, 'r') as f:
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

            task = {
                'task_id': task_id,
                'priority': task_data['priority'],
                'task_name': task_name,
                'status': task_data['status'],
                'description': escaped_description,
                'target_file': task_data.get('target_file')
            }
            tasks.append(task)
        return tasks

    def _is_valid_task_id(self, task_id):
        """Validates task_id to ensure it only contains allowed characters and format."""
        if not isinstance(task_id, str):
            return False
        # Allow alphanumeric, underscores, and hyphens, must start with alphanumeric
        # Disallow dots (.) in task IDs as they are used in file paths and could be confusing/risky
        # Updated regex to allow hyphens and underscores at the end
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
        if '..' in filename or '/' in filename or '\\' in filename:
            return False
        # Ensure it's not just a dot or dot-dot
        if filename in ['.', '..']:
            return False
        # Allow alphanumeric, underscores, hyphens, and dots. Must start with alphanumeric.
        # This regex is primarily for validating *user-provided* filenames/paths,
        # less critical for names from os.listdir if the base_path is trusted.
        # Let's simplify this check slightly for names from os.listdir, focusing on traversal.
        # A simple check for '..' and '/' might be sufficient here.
        # Re-using the task_id regex might be too strict for filenames.
        # Let's keep the previous regex but clarify its primary use case.
        # The regex `^[a-zA-Z0-9][a-zA-Z0-9_.-]*$` is suitable for file paths relative to the base.
        # Let's use this regex.
        return bool(re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9_.-]*$', filename))


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
        if not isinstance(filepath, str):
             logger.error(f"_write_output_file received non-string filepath: {type(filepath)}")
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
            if existing_content and not existing_content.strip().endswith('\n'): # Added strip() for robustness
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
                                'ethical_analysis_results'. (Security results are within code_review_results)

        Returns:
            A JSON string representing the Grade Report.
        """
        report = {
            "task_id": task_id,
            "timestamp": datetime.utcnow().isoformat(),
            "validation_results": {
                "tests": validation_results.get('test_results', {}),
                "code_review": validation_results.get('code_review_results', {}), # Includes static analysis and bandit
                "ethical_analysis": validation_results.get('ethical_analysis_results', {})
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
                "justification": f"Tests executed: {test_results.get('total')}, Passed: {test_results.get('passed')}, Failed: {test_results.get('failed')}, Status: {test_results.get('status')}"
            }
        elif test_results and test_results.get('status') == 'error':
             grades['test_success'] = {
                "percentage": 0,
                "justification": f"Test execution or parsing error: {test_results.get('message')}"
            }


        # Calculate Code Style Grade (10%) and Security Soundness Grade (20%)
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
        # FIX: Correct the key lookup from 'ethical_analysis' to 'ethical_analysis_results'
        ethical_results = validation_results.get('ethical_analysis_results') # CORRECTED KEY
        if ethical_results and ethical_results.get('overall_status') != 'error':
            percentage = 100 if ethical_results.get('overall_status') == 'approved' else 0
            justification = f"Ethical analysis status: {ethical_results.get('overall_status')}. Policy: {ethical_results.get('policy_name', 'N/A')}"
            if ethical_results.get('overall_status') == 'rejected':
                violations = [k for k, v in ethical_results.items() if isinstance(v, dict) and v.get('status') == 'violation']
                justification += f". Violations: {', '.join(violations)}"
            elif ethical_results.get('overall_status') == 'skipped':
                 percentage = 0 # Skipped is treated as 0 for grading
                 justification = f"Ethical analysis skipped: {ethical_results.get('message', 'Unknown reason')}"

            # FIX: Add the missing assignment here - THIS WAS ALREADY PRESENT, NO CHANGE NEEDED HERE
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
             "justification": "Non-regression testing is a placeholder. Graded based on Test Success (100% if tests passed, 0% otherwise)."
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

        logger.info(f"Grade Report Metrics: Overall Grade={overall_percentage_grade}%, Test Status={test_results.get('status')}, Ethical Status={ethical_analysis_results.get('overall_status')}, Code Review Status={code_review_results.get('status')}")

        recommended_action = "Manual Review Required"
        justification = "Default action based on unhandled scenario."

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