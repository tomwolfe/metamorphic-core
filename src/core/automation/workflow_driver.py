import logging
import os
import re

class WorkflowDriver:
    def __init__(self):
        pass

    def __repr__(self):
        return f"<{self.__class__.__name__} instance>"

    def load_roadmap(self, roadmap_path):
        """
        Loads and parses the ROADMAP.md file.

        Args:
            roadmap_path (str): The path to the ROADMAP.md file.

        Returns:
            list: A list of dictionaries, where each dictionary represents a task from the ROADMAP.md file.
                  Returns an empty list if the file is not found or if an error occurs during parsing.
        """
        try:
            with open(roadmap_path, 'r') as f:
                content = f.read()
                tasks = []
                task_pattern = re.compile(
                    r'\*\s+\*\*Task ID\*\*\:\s*(?P<task_id>.*?)\n'
                    r'\s*\*\s+\*\*Priority\*\*\:\s*(?P<priority>.*?)\n'
                    r'\s*\*\s+\*\*Task Name\*\*\:\s*(?P<task_name>.*?)\n'
                    r'\s*\*\s+\*\*Status\*\*\:\s*(?P<status>.*?)\n',
                    re.DOTALL
                )
                for match in task_pattern.finditer(content):
                    task = {
                        "task_id": match.group("task_id").strip(),
                        "priority": match.group("priority").strip(),
                        "task_name": match.group("task_name").strip(),
                        "status": match.group("status").strip(),
                    }
                    tasks.append(task)

                return tasks
        except FileNotFoundError:
            logging.error(f"ROADMAP.md file not found at path: {roadmap_path}")
            return []
        except Exception as e:
            logging.exception(f"Error loading or parsing ROADMAP.md: {e}")
            return []

    def list_files(self):
        """
        Lists all Python files in the current directory.

        Returns:
            list: A list of strings, where each string is the name of a Python file.
                  Returns an empty list if no Python files are found or if an error occurs.
        """
        try:
            python_files = [f for f in os.listdir('.') if f.endswith('.py')]
            return python_files
        except Exception as e:
            logging.exception(f"Error listing files: {e}")
            return []