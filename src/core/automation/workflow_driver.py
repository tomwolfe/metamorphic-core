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
from src.cli.write_file import write_file # Ensure write_file is imported

logger = logging.getLogger(__name__)

class Context:
    def __init__(self, base_path):
        self.base_path = base_path

    def get_full_path(self, relative_path):
        return os.path.join(self.base_path, relative_path)

class WorkflowDriver:
    def __init__(self, context: Context):
        self.context = context
        self.tasks = [] # Placeholder - will be loaded by CLI or other mechanism

        # Initialize LLM Orchestrator - Pass placeholder dependencies for now
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=MagicMock(),
            ethics_engine=MagicMock()
        )

    def autonomous_loop(self):
        """
        Main control flow loop for the autonomous Driver LLM.

        This method orchestrates the task selection, planning, agent invocation,
        and file management steps to drive the development process autonomously.
        """
        while True:
            logger.info('Starting autonomous loop iteration')

            next_task = self.select_next_task(self.tasks)

            if next_task:
                task_id = next_task.get('task_id', 'Unknown ID')
                logger.info(f'Selected task: ID={task_id}')

                solution_plan = self.generate_solution_plan(next_task)
                logger.info(f'Generated plan: {solution_plan}')

                # --- Task 15_3d: Integrate agent invocation based on the plan ---
                # --- Task 15_3e: Integrate file management into autonomous loop ---
                if solution_plan:
                    logger.info(f"Executing plan for task {task_id} with {len(solution_plan)} steps.")
                    for step_index, step in enumerate(solution_plan):
                        logger.info(f"Executing step {step_index + 1}/{len(solution_plan)}: {step}")

                        step_lower = step.lower() # Convert step to lower once
                        code_generation_keywords = ["implement", "generate code", "write function", "modify file", "add logic to"]
                        file_writing_keywords = ["write file", "create file", "save to file", "output file", "generate file"]

                        needs_coder_llm = any(keyword in step_lower for keyword in code_generation_keywords)

                        # Check for a file path match using the regex
                        # Revised regex to be less strict with word boundaries and allow slashes/dots in the path part
                        filepath_match = re.search(r'(\S+\.(py|md|json|txt|yml|yaml))', step, re.IGNORECASE) # <-- Updated regex
                        has_filepath = filepath_match is not None
                        filepath = filepath_match.group(1) if has_filepath else None # Extract filepath here if found

                        # A step is considered a file writing step if it contains a file path OR file writing keywords
                        is_file_writing_step = has_filepath or any(keyword in step_lower for keyword in file_writing_keywords)

                        generated_output = None # Initialize generated_output for this step

                        if needs_coder_llm:
                            logger.info(f"Step identified as potential code generation. Invoking Coder LLM for step: {step}")
                            # Construct a prompt specific to this step and the overall task
                            # NOTE: Task name and step are NOT sanitized here, potential prompt injection risk if roadmap is untrusted.
                            # Description is escaped by load_roadmap.
                            coder_prompt = f"""You are a Coder LLM expert in Python.
Your task is to perform the following specific step from a larger development plan for the task "{next_task.get('task_name', 'Unknown Task')}":

Overall Task Description:
{next_task.get('description', 'No description provided.')}

Specific Plan Step to Implement:
{step}

Please provide the Python code or necessary instructions to fulfill this step. Focus ONLY on the code or direct instructions needed for this step.
"""
                            generated_output = self._invoke_coder_llm(coder_prompt)

                            if generated_output:
                                logger.info(f"Coder LLM invoked for step {step_index + 1}. Generated output (first 100 chars): {generated_output[:100]}...")
                            else:
                                logger.warning(f"Coder LLM invocation for step {step_index + 1} returned no output.")

                        # --- File Writing Logic (Task 15_3e) ---
                        if is_file_writing_step:
                             logger.info(f"Step identified as file writing. Processing file operation for step: {step}")

                             if filepath: # Proceed with writing ONLY if a filepath was found
                                 content = None # Initialize content

                                 if needs_coder_llm and generated_output:
                                     content = generated_output
                                     logger.info(f"Using generated code for file: {filepath}")
                                 else:
                                     content = f"// Placeholder content for step: {step}"
                                     logger.info(f"Using placeholder content for file: {filepath}")

                                 if content is not None:
                                     logger.info(f"Attempting to write file: {filepath}")
                                     try:
                                         self._write_output_file(filepath, content, overwrite=False)
                                     except FileExistsError:
                                         logger.warning(f"File {filepath} already exists. Skipping write as overwrite=False.")
                                     except Exception as e:
                                         logger.error(f"Failed to write file {filepath}: {e}", exc_info=True)
                                 else:
                                     logger.warning(f"Content is None for file {filepath}. Skipping file write.")

                             else:
                                 logger.warning(f"Could not extract filepath from step '{step}'. Skipping file write.")


                        # Log if *neither* code generation nor file writing was identified
                        if not needs_coder_llm and not is_file_writing_step:
                            logger.info(f"Step not identified as code generation or file writing. Skipping agent invocation/file write for step: {step}")

                else:
                    logger.warning(f"No solution plan generated for task {task_id}.")

            else:
                logger.info('No tasks available in Not Started status. Exiting autonomous loop.')
                break

        logger.info('Autonomous loop terminated.')

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

        planning_prompt = f"""You are an AI assistant specializing in software development workflows.
Your task is to generate a step-by-step solution plan for the following development task from the Metamorphic Software Genesis Ecosystem roadmap.

Task Name: {task_name}
Task Description:
{description}

The plan should be a numbered list of concise steps (1-2 sentences each). Focus on the high-level actions needed to complete the task. Include steps for writing files where appropriate, explicitly mentioning the file path (e.g., "Write code to file src/module/new_file.py").

Example Plan Format:
1.  Analyze the requirements for X.
2.  Modify the Y component (src/component/y.py).
3.  Implement Z feature.
4.  Write tests for the changes (tests/test_z_feature.py).
5.  Update documentation (docs/feature_z.md).

Please provide the plan as a numbered markdown list. Do not include any introductory or concluding remarks outside the list.
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
        """
        Invokes the Coder LLM (LLMOrchestrator) to generate code or text.

        Args:
            coder_llm_prompt: The prompt to send to the Coder LLM.

        Returns:
            Return the generated text from the LLM, or None if there was an error.
        """
        try:
            response = self.llm_orchestrator.generate(coder_llm_prompt)
            if response is None:
                 logger.error("LLM Orchestrator generate method returned None.")
                 return None
            return response.strip()
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
            markdown_steps += f"{i+1}.  - [ ] {html.escape(step)}\n"
        return markdown_steps

    def load_roadmap(self, roadmap_file_path):
        tasks = []
        max_file_size = 10000
        if not os.path.exists(roadmap_file_path):
            logger.error(f"ROADMAP.json file not found at path: {roadmap_file_path}")
            return tasks

        if os.path.getsize(roadmap_file_path) > max_file_size:
            logger.error(f"ROADMAP.json file exceeds maximum allowed size of {max_file_size} bytes.")
            return tasks

        try:
            with open(roadmap_file_path, 'r') as f:
                roadmap_data = json.load(f)
        except json.JSONDecodeError:
            logger.error(f"Invalid JSON in roadmap file: {roadmap_file_path}")
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

            task = {
                'task_id': task_id,
                'priority': task_data['priority'],
                'task_name': task_name,
                'status': task_data['status'],
                'description': escaped_description,
            }
            tasks.append(task)
        return tasks

    def _is_valid_task_id(self, task_id):
        """Validates task_id to ensure it only contains allowed characters and format."""
        if not isinstance(task_id, str):
            return False
        # Allow alphanumeric, underscores, and hyphens, must start with alphanumeric
        return bool(re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9_-]*$', task_id))


    def file_exists(self, relative_file_path):
        """Checks if a file exists in the workspace."""
        try:
            full_path = self.context.get_full_path(relative_file_path)
            resolved_path = Path(full_path).resolve()
            resolved_base_path = Path(self.context.base_path).resolve()
            if not str(resolved_path).startswith(str(resolved_base_path)):
                 logger.warning(f"Attempted to check file existence outside base path: {relative_file_path} (Resolved: {resolved_path})")
                 return False
            return os.path.exists(resolved_path) and os.path.isfile(resolved_path)
        except Exception as e:
            logger.error(f"Error checking file existence for {relative_file_path}: {e}", exc_info=True)
            return False

    def list_files(self):
        """Lists files and directories in the workspace root."""
        base_path = self.context.base_path
        entries = []
        try:
            resolved_base_path = Path(base_path).resolve()
            if not resolved_base_path.is_dir():
                 logger.error(f"Base path is not a valid directory: {base_path}")
                 return []

            for name in os.listdir(resolved_base_path):
                full_path = os.path.join(resolved_base_path, name)
                if not self._is_valid_filename(name):
                     logger.warning(f"Skipping listing of invalid filename: {name}")
                     continue

                if os.path.isfile(full_path):
                    entries.append({'name': name, 'status': 'file'})
                elif os.path.isdir(full_path):
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
        if '..' in filename or '/' in filename or '\\' in filename:
            return False
        # Allow alphanumeric, underscores, hyphens, dots (for extensions)
        # Ensure it's not just a dot or dot-dot
        if filename in ['.', '..']:
            return False
        return bool(re.fullmatch(r'^[a-zA-Z0-9_.-]+$', filename))


    def _write_output_file(self, filepath, content, overwrite=False):
        """
        Writes content to a file using the write_file utility function.

        Args:
            filepath (str): The path to the file.
            content (str): The content to write.
            overwrite (bool): Whether to overwrite existing files. Defaults to False.

        Returns:
            bool: True if file writing was successful, False otherwise.

        Raises:
            FileExistsError: If overwrite is False and the file already exists.
        """
        try:
            # Resolve the path relative to the base_path first, then resolve the full path
            full_path = self.context.get_full_path(filepath)
            resolved_filepath = Path(full_path).resolve()
        except Exception as e:
            logger.error(f"Error resolving filepath {filepath}: {e}", exc_info=True)
            return False

        resolved_base_path = Path(self.context.base_path).resolve()
        # Ensure the resolved path is within the resolved base path
        if not str(resolved_filepath).startswith(str(resolved_base_path)):
             logger.error(f"Attempt to write outside base path: {filepath} (Resolved: {resolved_filepath})")
             return False

        try:
            # Pass the resolved full path to write_file
            result = write_file(str(resolved_filepath), content, overwrite=overwrite)
            if result:
                logger.info(f"Successfully wrote to file: {resolved_filepath}")
                return True
            return False
        except FileExistsError as e:
            logger.warning(f"File already exists and overwrite is False: {resolved_filepath}")
            raise e
        except FileNotFoundError as e:
            logger.error(f"File not found error when writing to {filepath}: {e}", exc_info=True)
            return False
        except PermissionError as e:
            logger.error(f"Permission error when writing to {filepath}: {e}", exc_info=True)
            return False
        except Exception as e:
            logger.error(f"Unexpected error writing to {filepath}: {e}", exc_info=True)
            return False