import logging
import os

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
                # Implement parsing logic here based on the structure of your ROADMAP.md
                # This is a basic placeholder; you'll need to adapt it to your specific format.
                tasks = []
                lines = content.splitlines()
                for line in lines:
                    if line.startswith("*   **Task ID**"):
                        task_id = line.split(":")[1].strip()
                        priority_line = next((l for l in lines if lines.index(l) > lines.index(line) and l.startswith("*   **Priority**")), None)
                        task_name_line = next((l for l in lines if lines.index(l) > lines.index(line) and l.startswith("*   **Task Name**")), None)
                        status_line = next((l for l in lines if lines.index(l) > lines.index(line) and l.startswith("*   **Status**")), None)

                        priority = priority_line.split(":")[1].strip() if priority_line else ""
                        task_name = task_name_line.split(":")[1].strip() if task_name_line else ""
                        status = status_line.split(":")[1].strip() if status_line else ""
                        task = {
                            "task_id": task_id,
                            "priority": priority,
                            "task_name": task_name,
                            "status": status,
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