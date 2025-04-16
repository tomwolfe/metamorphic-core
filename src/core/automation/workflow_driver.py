# src/core/automation/workflow_driver.py

from src.cli.write_file import write_file  # Import the utility function for writing files
import logging  # Import the logging module for logging messages
import html
import os
import json # Import JSON
from pathlib import Path

# Configure the logger
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

    def select_next_task(self, tasks: list) -> dict | None:
        """Selects the next task with status 'Not Started' from the list.

        Args:
            tasks: A list of task dictionaries. Each task must contain a 'status' key.

        Returns:
            The first task dictionary with a status of 'Not Started', or None if no such task exists or the list is empty.
        """
        for task in tasks:
            if task['status'] == 'Not Started':
                return task
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
            markdown_steps += f"{i+1}.  - [ ] {html.escape(step)}\n" # Note: html.escape is used here
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
            if not self._is_valid_task_id(task_id):
                logger.warning(f"Invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
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
                'description': escaped_description, # Use escaped description here for roadmap loading
            }
            tasks.append(task)
        return tasks

    def _is_valid_task_id(self, task_id):
        """Validates task_id to ensure it only contains allowed characters."""
        allowed_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-"
        return all(char in allowed_chars for char in task_id)

    def file_exists(self, relative_file_path):
        """Checks if a file exists in the workspace."""
        full_path = self.context.get_full_path(relative_file_path)
        return os.path.exists(full_path) and os.path.isfile(full_path)

    def list_files(self):
        """Lists files and directories in the workspace root."""
        base_path = self.context.base_path
        entries = []
        for name in os.listdir(base_path):
            full_path = os.path.join(base_path, name)
            if os.path.isfile(full_path):
                entries.append({'name': name, 'status': 'file'})
            elif os.path.isdir(full_path):
                entries.append({'name': name, 'status': 'directory'})
        return entries

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
        sanitized_filepath = str(Path(filepath).resolve()) # Sanitize the filepath
        if not sanitized_filepath.startswith(self.context.base_path):
             logger.error(f"Attempt to write outside base path: {filepath} (Sanitized: {sanitized_filepath})")
             return False

        try:
            # Call the write_file function with the provided parameters
            result = write_file(sanitized_filepath, content, overwrite=overwrite)
            
            # If write_file succeeds, log an info message and return True
            if result:
                logger.info(f"Successfully wrote to file: {sanitized_filepath}")
                return True
            
            # If write_file returns False, propagate the failure
            return False

        except FileExistsError as e:
            # Propagate FileExistsError to allow the caller to handle it
            raise e

        except FileNotFoundError as e:
            # Log an error message for FileNotFoundError
            logger.error(f"File not found error when writing to {filepath}: {e}", exc_info=True) #Include exception
            return False

        except PermissionError as e:
            # Log an error message for PermissionError
            logger.error(f"Permission error when writing to {filepath}: {e}", exc_info=True) #Include exception
            return False

        except Exception as e:
            # Log any unexpected exceptions
            logger.error(f"Unexpected error writing to {filepath}: {e}", exc_info=True) #Include exception
            return False