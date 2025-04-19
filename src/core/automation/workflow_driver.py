# src/core/automation/workflow_driver.py
from src.cli.write_file import write_file
import logging
import html
import os
import json
from pathlib import Path
from src.core.llm_orchestration import EnhancedLLMOrchestrator  # Added import
import re # Import regex for task_id validation

logger = logging.getLogger(__name__)

class Context:
    def __init__(self, base_path):
        self.base_path = base_path

    def get_full_path(self, relative_path):
        return os.path.join(self.base_path, relative_path)

class WorkflowDriver:
    def __init__(self, context: Context):
        # Initialize the WorkflowDriver with a given context
        self.context = context
        # NOTE: self.tasks will need to be loaded before autonomous_loop is called
        # This will be addressed in a later task. For now, assume self.tasks is available.
        self.tasks = [] # Placeholder - will be loaded by CLI or other mechanism

        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=None,  # Will be properly initialized in later phases
            spec=None,  # Will be properly initialized in later phases
            ethics_engine=None  # Will be properly initialized in later phases
        )

    def autonomous_loop(self):
        """
        Main control flow loop for the autonomous Driver LLM.

        This method orchestrates the task selection, planning, agent invocation,
        and file management steps to drive the development process autonomously.
        """
        while True: # Loop indefinitely until explicitly broken
            logger.info('Starting autonomous loop iteration') # Changed log message slightly for clarity

            # Call select_next_task to get the next task
            # Ensure self.tasks is populated before calling select_next_task in a real scenario
            # In a real scenario, self.tasks would be loaded once before the loop starts
            next_task = self.select_next_task(self.tasks)

            # Log the selected task or indicate no tasks are available
            if next_task:
                # Ensure task_id is accessed safely
                task_id = next_task.get('task_id', 'Unknown ID')
                logger.info(f'Selected task: ID={task_id}')

                # Call generate_solution_plan and log the result
                solution_plan = self.generate_solution_plan(next_task) # Call the placeholder method
                logger.info(f'Generated plan: {solution_plan}') # Log the result

                # --- Future steps will process this task (Task 15_3c, 15_3d, etc.) ---
                # For now, the loop will continue to the next iteration after processing a task.
                # A real implementation might update task status here and re-select.

            else:
                logger.info('No tasks available in Not Started status. Exiting autonomous loop.')
                break # Exit the loop when no tasks are found

            # Removed the unconditional break here

        logger.info('Autonomous loop terminated.') # Added log message for loop termination


    def generate_solution_plan(self, task: dict) -> list[str]:
        """
        Placeholder method to generate a solution plan for a given task.

        Args:
            task: The task dictionary for which to generate a plan.

        Returns:
            A hardcoded list of strings representing a simple plan.
        """
        # This is a placeholder implementation. Actual plan generation
        # using LLMs will be implemented in a later task (Task 15_3c).
        logger.debug(f"Generating placeholder plan for task: {task.get('task_id', 'Unknown ID')}")
        return ['Placeholder Step 1', 'Placeholder Step 2']


    def _invoke_coder_llm(self, coder_llm_prompt: str) -> str:
        """
        Invokes the Coder LLM (LLMOrchestrator) to generate code.

        Args:
            coder_llm_prompt: The prompt to send to the Coder LLM.

        Returns:
            The generated code from the Coder LLM, or None if there was an error.
        """
        try:
            # Use the mocked or real llm_orchestrator instance
            response = self.llm_orchestrator.generate(coder_llm_prompt)
            return response.strip()  # Return the generated code, stripped of whitespace
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
        # Add input validation for safety and robustness
        if not isinstance(tasks, list):
            logger.warning(f"select_next_task received non-list input: {type(tasks)}")
            return None # Return None for invalid input

        for task in tasks:
            # Ensure task is a dictionary and has required keys for safe access
            if isinstance(task, dict) and 'status' in task and 'task_id' in task:
                # Basic sanitization/validation of task_id to prevent path traversal
                task_id = task.get('task_id')
                if task['status'] == 'Not Started':
                    if task_id and self._is_valid_task_id(task_id):
                         return task
                    elif task_id:
                         logger.warning(f"Skipping task with invalid task_id format: {task_id}")
                    # If task_id is missing or invalid, continue to next task
            else:
                # Log a warning for tasks that are not dictionaries or missing keys
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
            # Use html.escape for sanitization to prevent rendering issues in markdown
            markdown_steps += f"{i+1}.  - [ ] {html.escape(step)}\n"
        return markdown_steps

    def load_roadmap(self, roadmap_file_path):
        tasks = []
        max_file_size = 10000  # Maximum file size in bytes (10KB)
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
            # Validate task_id format early
            if not self._is_valid_task_id(task_id):
                logger.warning(f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue

            task_name = task_data['task_name']
            if len(task_name) > 150:
                logger.warning(f"Task Name '{task_name}' exceeds 150 characters. Task will be skipped.")
                continue

            task_description = task_data['description']
            # Sanitize description to prevent rendering issues in markdown/HTML
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
        # Regex allows alphanumeric, underscores, and hyphens, but must start with alphanumeric.
        # Prevents '/', '\', '..', '.', leading/trailing hyphens/underscores (implicitly by requiring alphanumeric start)
        # Corrected regex to match test expectations (start with alphanumeric)
        return bool(re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9_-]*$', task_id))


    def file_exists(self, relative_file_path):
        """Checks if a file exists in the workspace."""
        # Sanitize path before checking existence
        try:
            full_path = self.context.get_full_path(relative_file_path)
            resolved_path = Path(full_path).resolve()
            # Ensure the resolved path is still within the base path for security
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
            # Ensure base_path is resolved and valid before listing
            resolved_base_path = Path(base_path).resolve()
            if not resolved_base_path.is_dir():
                 logger.error(f"Base path is not a valid directory: {base_path}")
                 return []

            for name in os.listdir(resolved_base_path):
                full_path = os.path.join(resolved_base_path, name)
                # Further sanitize/validate each entry name if necessary, though os.listdir is relatively safe
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
        # Prevent names containing path traversal sequences or control characters
        if '..' in filename or '/' in filename or '\\' in filename:
            return False
        # Add other checks as needed (e.g., control characters)
        return True


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
        # Sanitize the filepath and resolve it to an absolute path
        try:
            resolved_filepath = Path(filepath).resolve()
        except Exception as e:
            logger.error(f"Error resolving filepath {filepath}: {e}", exc_info=True)
            return False

        # Ensure the resolved path is within the base path for security
        resolved_base_path = Path(self.context.base_path).resolve()
        if not str(resolved_filepath).startswith(str(resolved_base_path)):
             logger.error(f"Attempt to write outside base path: {filepath} (Resolved: {resolved_filepath})")
             return False

        try:
            # Call the write_file function with the sanitized and validated path
            result = write_file(str(resolved_filepath), content, overwrite=overwrite)

            # If write_file succeeds, log an info message and return True
            if result:
                logger.info(f"Successfully wrote to file: {resolved_filepath}")
                return True

            # If write_file returns False (e.g., due to internal error not raising exception), propagate the failure
            return False

        except FileExistsError as e:
            # Propagate FileExistsError to allow the caller to handle it
            logger.warning(f"File already exists and overwrite is False: {resolved_filepath}")
            raise e

        except FileNotFoundError as e:
            # Log an error message for FileNotFoundError
            logger.error(f"File not found error when writing to {filepath}: {e}", exc_info=True)
            return False

        except PermissionError as e:
            # Log an error message for PermissionError
            logger.error(f"Permission error when writing to {filepath}: {e}", exc_info=True)
            return False

        except Exception as e:
            # Log any unexpected exceptions
            logger.error(f"Unexpected error in _write_output_file for {filepath}: {e}", exc_info=True)
            return False