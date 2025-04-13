# src/core/automation/workflow_driver.py
import logging
import os
import json
import html
from typing import List  # Added this line

class Context:  # Added Context class
    def __init__(self, root_dir):
        self.root_dir = root_dir

class WorkflowDriver:
    def __init__(self, context):  # Modified constructor
        self.context = context

    def __repr__(self):
        return f"<{self.__class__.__name__} instance>"

    def load_roadmap(self, roadmap_path):
        tasks = []
        max_file_size = 1024 * 10  # 10KB limit
        try:
            # Check file extension first
            if not roadmap_path.lower().endswith('.json'):
                logging.error("ROADMAP must be a .json file")
                return []
            if os.path.getsize(roadmap_path) > max_file_size:
                logging.error(f"ROADMAP.json file exceeds maximum allowed size of {max_file_size} bytes.")
                return []

            with open(roadmap_path, 'r') as f:
                content = f.read()
            try:
                data = json.loads(content)
            except json.JSONDecodeError as e:
                logging.error(f"Invalid JSON in roadmap file: {e}")
                return []
            # Ensure data is a dictionary with 'tasks' key
            if not isinstance(data, dict):
                logging.error("ROADMAP.json must be a valid JSON object (dictionary)")
                return []
            # Validate 'tasks' exists and is a list
            if 'tasks' not in data:
                logging.error("ROADMAP.json must contain a 'tasks' key")
                return []
            if not isinstance(data['tasks'], list):
                logging.error("'tasks' must be a list")
                return []
            for task in data['tasks']:
                if not isinstance(task, dict):
                    logging.warning("Skipping invalid task (not a dictionary)")
                    continue
                # Check required fields
                required_keys = ['task_id', 'priority', 'task_name']
                if not all(k in task for k in required_keys):
                    missing = [k for k in required_keys if k not in task]
                    logging.warning(f"Task missing required keys: {missing}. Skipping task.")
                    continue
                # Validate task_id
                task_id = task['task_id'].strip()
                if not task_id or '/' in task_id or '..' in task_id:
                    logging.warning(f"Invalid task_id '{task_id}'. Skipping.")
                    continue
                # Validate task_name length
                task_name = task['task_name'].strip()
                if len(task_name) > 150:
                    logging.warning(f"Task Name '{task_name[:50]}...' exceeds 150 characters, skipping task.")
                    continue
                # Provide default status if missing
                status = task.get('status', '').strip()
                # Sanitize description
                description = html.escape(task.get('description', ''))  # Escape HTML to prevent XSS
                tasks.append({
                    'task_id': task_id,
                    'priority': task['priority'],
                    'task_name': task_name,
                    'status': status,
                    'description': description
                })
            return tasks
        except FileNotFoundError:
            logging.error(f"ROADMAP.json file not found at path: {roadmap_path}")
            return []
        except Exception as e:
            logging.exception(f"Error loading roadmap: {e}")
            return []

    def file_exists(self, file_path: str) -> bool:
        return os.path.exists(file_path)

    def list_files(self):
        try:
            entries = os.listdir(self.context.root_dir)
        except Exception as e:
            logging.error(f"Error listing files in {self.context.root_dir}: {e}")
            return None
        result = []
        for entry in entries:
            full_path = os.path.join(self.context.root_dir, entry)
            if os.path.isfile(full_path):
                result.append({'name': entry, 'status': 'file'})
            elif os.path.isdir(full_path):
                result.append({'name': entry, 'status': 'directory'})
            else:
                # Handle other types (e.g., symlinks, character devices)
                logging.warning(f"Skipping unknown file type: {entry}")
                # Optionally, add a default status
                # result.append({'name': entry, 'status': 'unknown'})  # OPTIONAL append for all unknown entries
        return result

    def generate_user_actionable_steps(self, solution_plan: List[str]) -> str:
        """Formats each step in the solution plan into a numbered Markdown checklist.

        Args:
            solution_plan (list of str): A list of steps to be formatted into a checklist.

        Returns:
            str: A single string containing the formatted checklist with each step as a numbered item.

        Raises:
            TypeError: If the input is not a list of strings.
        """
        # Validate input type to prevent code injection and ensure correctness
        if not isinstance(solution_plan, list) or not all(isinstance(step, str) for step in solution_plan):
            raise TypeError("Input must be a list of strings")

        if not solution_plan:  # Added check for empty list
            return ""

        formatted_steps = []
        for index, step in enumerate(solution_plan, 1):
            # Safely format each step with numbered checklist syntax
            formatted_step = f"{index}.  - [ ] {html.escape(step)}\n"
            formatted_steps.append(formatted_step)

        # Join all formatted steps into a single string with newlines
        return "".join(formatted_steps)

    def generate_coder_llm_prompts(self, task: dict, solution_plan: list) -> List[str]:
        """
        Generates precise code generation prompts for the Coder LLM based on the task and solution plan.

        Args:
            task (dict): A dictionary containing the task details (task_name, description, etc.).
            solution_plan (list): A list of strings representing the high-level solution plan.

        Returns:
            List[str]: A list containing the generated Coder LLM prompts (currently a list with a single prompt).

        Raises:
            TypeError: If inputs are not of the correct type.
            ValueError: If task dictionary is missing required keys.
        """
        if not isinstance(task, dict):
            raise TypeError("Input 'task' must be a dictionary")
        if not isinstance(solution_plan, list) or not all(isinstance(item, str) for item in solution_plan):
            raise TypeError("Input 'solution_plan' must be a list of strings")
        if 'task_name' not in task or 'description' not in task:
            raise ValueError("Task dictionary must contain 'task_name' and 'description' keys")

        task_name = task['task_name']
        task_description = html.escape(task['description'])
        solution_plan = [html.escape(step) for step in solution_plan]

        prompt_header = f"You are a Coder LLM expert in Python, asked to implement code for the following task:\\n\\n"
        prompt_task_details = f"Task Name: {task_name}\\nTask Description: {task_description}\\n\\n"
        prompt_plan_intro = "Solution Plan:\\n"
        prompt_plan_steps = "\\n".join([f"- {step}" for step in solution_plan])
        prompt_requirements = "\\n\\nRequirements:\\n- Write secure and well-documented Python code.\\n- Follow best practices for code quality and style.\\n- Prioritize security, and prevent code injection vulnerabilities.\\n"

        full_prompt = prompt_header + prompt_task_details + prompt_plan_intro + prompt_plan_steps + prompt_requirements

        return [full_prompt]