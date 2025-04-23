# workflow_driver.py
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

logger = logging.getLogger(__name__)

# Define a maximum file size for reading (e.g., 1MB)
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB


class Context:
    def __init__(self, base_path):
        self.base_path = base_path

    def get_full_path(self, relative_path):
        """Resolves a relative path against the context's base path."""
        if not isinstance(relative_path, str):
             # Handle non-string input gracefully
             return None
        try:
            # Use Path.resolve() to handle '..' and symlinks safely
            # Check if the resolved path is still within the base path
            full_requested_path = Path(self.base_path) / relative_path
            resolved_path = full_requested_path.resolve()
            resolved_base_path = Path(self.base_path).resolve()

            if not str(resolved_path).startswith(str(resolved_base_path)):
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

        # Initialize LLM Orchestrator - Pass placeholder dependencies for now
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=MagicMock(),
            ethics_engine=MagicMock()
        )

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
        if not hasattr(self, 'roadmap_path') or not self.roadmap_path:
            logger.error("Roadmap path not set. Cannot start autonomous loop.")
            return # Exit if roadmap path is not set

        while True:
            logger.info('Starting autonomous loop iteration')

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

                        generated_output = None  # Initialize generated_output for this step
                        content_to_write = None # Initialize content_to_write
                        overwrite_file = False # Initialize overwrite flag

                        # --- Logic for steps involving the Coder LLM ---
                        # Only invoke Coder if code gen is needed AND we know which file
                        if needs_coder_llm and filepath_to_use:
                            logger.info(
                                f"Step identified as potential code generation for file {filepath_to_use}. Invoking Coder LLM for step: {step}")

                            # Read existing content if the file exists using the new robust method
                            existing_content = self._read_file_for_context(filepath_to_use)

                            # --- MODIFIED PROMPT CONSTRUCTION ---
                            # Construct the detailed prompt here, including task context, step, and existing content
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
                            # --- END MODIFIED PROMPT CONSTRUCTION ---

                            # --- DEBUG LOGS ADDED HERE ---
                            logger.debug("Entering _invoke_coder_llm call block.")
                            logger.debug("Calling _invoke_coder_llm with prompt: %s", coder_prompt[:500])
                            # --- END DEBUG LOGS ---

                            generated_output = self._invoke_coder_llm(coder_prompt) # Pass the constructed prompt

                            if generated_output:
                                logger.info(
                                    f"Coder LLM invoked for step {step_index + 1}. Generated output (first 100 chars): {generated_output[:100]}...")
                                # Use generated output as the content to merge/write

                                # --- START MODIFIED LOGIC FOR SNIPPET MERGING AND WRITING ---
                                # We generated a snippet. Now merge it into the existing content.
                                merged_content = self._merge_snippet(existing_content, generated_output)
                                logger.info(f"Merged snippet into {filepath_to_use}. Attempting to write merged content.")

                                # Write the merged content back to the file, overwriting the original
                                try:
                                    self._write_output_file(filepath_to_use, merged_content, overwrite=True)
                                    logger.info(f"Successfully wrote merged content to {filepath_to_use}.")
                                except FileExistsError:
                                    # This should not happen with overwrite=True, but handle defensively
                                    logger.error(f"Unexpected FileExistsError when writing merged content to {filepath_to_use} with overwrite=True.")
                                except Exception as e:
                                    logger.error(f"Failed to write merged content to {filepath_to_use}: {e}", exc_info=True)
                                # --- END MODIFIED LOGIC ---


                        # --- File Writing Logic (Adjusted for Snippet Generation) ---
                        # This logic should now only handle steps that are *explicitly* file writing
                        # but *not* code generation steps that produce snippets.
                        # The logic for writing the *merged* file content will be added in task_1_6_integrate_file_flow.
                        # For *this* task, if needs_coder_llm was true, we just generated a snippet and logged it.
                        # If needs_coder_llm is false, but it's a file writing step, we use placeholder content.
                        # The original logic below is mostly correct for non-code-gen file writes,
                        # but needs to be careful not to trigger for the snippet case.

                        elif is_file_writing_step and not needs_coder_llm and filepath_to_use:
                             logger.info(f"Step identified as file writing (placeholder). Processing file operation for step: {step}")
                             content_to_write = f"// Placeholder content for step: {step}"
                             logger.info(f"Using placeholder content for file: {filepath_to_use}")
                             logger.info(f"Attempting to write file: {filepath_to_use}")
                             try:
                                 # Use overwrite=False for placeholder content
                                 self._write_output_file(filepath_to_use, content_to_write, overwrite=False)
                             except FileExistsError:
                                 logger.warning(
                                     f"File {filepath_to_use} already exists. Skipping write as overwrite=False.")
                             except Exception as e:
                                 logger.error(f"Failed to write file {filepath_to_use}: {e}",
                                              exc_info=True)

                        elif is_file_writing_step and not filepath_to_use and not needs_coder_llm:
                             # This case is for file writing steps where no specific file was identified and no code gen
                             logger.warning(
                                 f"Could not determine filepath for step '{step}'. Skipping file write.")

                        # Log if *neither* code generation nor file writing was identified
                        # This log message is now less relevant if target_file is used,
                        # but keep it for steps that truly don't involve file writing or code gen.
                        # The condition `not needs_coder_llm and not is_file_writing_step` still works.
                        if not needs_coder_llm and not is_file_writing_step:
                            logger.info(
                                f"Step not identified as code generation or file writing. Skipping agent invocation/file write for step: {step}")


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
            resolved_path = Path(full_path).resolve()
        except Exception as e:
            logger.error(f"Error resolving filepath {relative_file_path} for existence check: {e}",
                         exc_info=True)
            return False

        # No need to check startswith(resolved_base_path) here because context.get_full_path
        # and Path.resolve() handle '..' and absolute paths relative to the base path.
        # Path.resolve() will raise if the path doesn't exist or can't be resolved.
        # The primary check is whether the resolved path actually exists and is a file.
        return os.path.exists(resolved_path) and os.path.isfile(resolved_path)

    def list_files(self):
        """Lists files and directories in the workspace root."""
        base_path = self.context.base_path
        entries = []
        try:
            resolved_base_path = Path(base_path).resolve()
            if not resolved_base_path.is_dir():
                logger.error(f"Base path is not a valid directory: {base_path}")
                return []

            # Use resolved_base_path for listing
            for name in os.listdir(resolved_base_path):
                full_path = resolved_base_path / name # Use Path object for joining
                # No need to validate filename here if we trust os.listdir and resolved_base_path
                # The _is_valid_filename check was primarily for user-provided paths.
                # However, keeping a basic check might be prudent if the environment is untrusted.
                # Let's simplify this check slightly for names from os.listdir, focusing on traversal.
                # A simple check for '..' and '/' might be sufficient here.
                # Re-using the task_id regex might be too strict for filenames.
                # Let's keep the previous regex but clarify its primary use case.
                # The regex `^[a-zA-Z0-9][a-zA-Z0-9_.-]*$` is suitable for file paths relative to the base.
                # Let's use this regex.
                if not self._is_valid_filename(name):
                     logger.warning(f"Skipping listing of potentially unsafe filename: {name}")
                     continue


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
            resolved_filepath = Path(full_path).resolve()
        except Exception as e:
            logger.error(f"Error resolving filepath {filepath} for writing: {e}", exc_info=True)
            return False

        # Ensure the resolved path is within the resolved base path (redundant if context.get_full_path is safe, but defensive)
        # resolved_base_path = Path(self.context.base_path).resolve()
        # if not str(resolved_filepath).startswith(str(resolved_base_path)):
        #     logger.error(f"Attempt to write outside base path: {filepath} (Resolved: {resolved_filepath})")
        #     return False

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

    # ADDED: Implementation of execute_tests method
    def execute_tests(self, test_command: list[str], cwd: str) -> tuple[str, str, int]:
        """
        Executes a given test command using subprocess with error handling.

        Args:
            test_command (list): The command and its arguments as a list.
                                 Example: ['pytest', 'tests/']
            cwd (str, optional): The current working directory to run the command from.
                                 Defaults to None (uses current process's cwd).

        Returns:
            tuple: A tuple containing (return_code, stdout, stderr).
                   return_code is 0 for success, non-zero for failure.
                   stdout and stderr are strings containing the captured output.
                   In case of execution errors (like command not found),
                   return_code will be non-zero, stdout will be empty,
                   and stderr will contain an error message.
        """
        stdout = ""
        stderr = ""
        return_code = 1 # Default to a non-zero failure code

        logger.info(f"Executing command: {' '.join(test_command)} in directory: {cwd or 'current directory'}")

        try:
            # Execute the command
            # capture_output=True captures stdout and stderr
            # text=True decodes stdout/stderr using default encoding
            # check=True raises CalledProcessError if the command returns a non-zero exit code
            process = subprocess.run(
                test_command,
                cwd=cwd,
                capture_output=True,
                text=True,
                check=False # Changed to False to avoid raising CalledProcessError
            )

            stdout = process.stdout
            stderr = process.stderr
            return_code = process.returncode

            if return_code == 0:
                 logger.info(f"Command executed successfully. Return code: {return_code}")
            else:
                 logger.warning(f"Command failed with return code: {return_code}")

            logger.debug(f"STDOUT:\n{stdout}")
            logger.debug(f"STDERR:\n{stderr}")

        except FileNotFoundError:
            # Handle the case where the command executable is not found
            stderr = f"Error: Command executable not found. Ensure '{test_command[0]}' is in your system's PATH."
            return_code = 127 # Standard error code for command not found
            logger.error(stderr)

        except Exception as e:
            # Catch any other unexpected errors during subprocess execution (e.g., permission errors, invalid arguments)
            stderr = f"An unexpected error occurred during command execution: {e}"
            return_code = 1 # Generic failure code

        return return_code, stdout, stderr # Corrected return order

    def _merge_snippet(self, existing_content: str, snippet: str) -> str:
        """
        Merges a generated code snippet into existing file content.

        For this basic implementation, the snippet is appended to the existing content.

        Args:
            existing_content: The current content of the file.
            snippet: The code snippet generated by the Coder LLM.

        Returns:
            The merged content as a string.
        """
        if not existing_content:
            return snippet
        # Add a newline for separation if existing content is not empty
        return existing_content + "\n" + snippet # Corrected logic