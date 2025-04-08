import logging
import os
import re

class WorkflowDriver:
    def __init__(self):
        pass

    def __repr__(self):
        return f"<{self.__class__.__name__} instance>"

    def load_roadmap(self, roadmap_path):
        tasks = []
        max_file_size = 1024 * 10  # 10KB limit
        try:
            if os.path.getsize(roadmap_path) > max_file_size:
                logging.error(f"ROADMAP.md file exceeds maximum allowed size of {max_file_size} bytes.")
                return []

            with open(roadmap_path, 'r') as f:
                content = f.read()

            # Regex to match individual task entries
            task_pattern = re.compile(
                r"\*\s+\*\*Task ID\*\*\:\s*(?P<task_id>.*?)\n"
                r"\s*\*\s+\*\*Priority\*\*\:\s*(?P<priority>.*?)\n"
                r"\s*\*\s+\*\*Task Name\*\*\:\s*(?P<task_name>.*?)\n"
                r"(?:\s*\*\s+\*\*Status\*\*\:\s*(?P<status>.*?)\n)?",
                re.DOTALL
            )

            # Find all matches of the task pattern
            matches = task_pattern.finditer(content)

            for match in matches:
                task_data = match.groupdict()
                task = {}

                # Safely extract and strip data using .get() and .strip()
                task_id = task_data.get('task_id')
                task['task_id'] = task_id.strip() if isinstance(task_id, str) else ""

                priority = task_data.get('priority')
                task['priority'] = priority.strip() if isinstance(priority, str) else ""

                task_name = task_data.get('task_name')

                if isinstance(task_name, str):
                    # Validate task name length
                    task_name = task_name.strip()  # strip here only when it is a string to avoid name errors
                    if len(task_name) > 150:
                        logging.warning(f"Task Name '{task_name[:50]}...' exceeds 150 characters, skipping task.")
                        continue # Skip the task if it violates length limits
                    task['task_name'] = task_name
                else:
                    task['task_name'] = ""

                status = task_data.get('status')
                task['status'] = status.strip() if isinstance(status, str) else ""

                tasks.append(task)

            return tasks

        except FileNotFoundError:
            logging.error(f"ROADMAP.md file not found at path: {roadmap_path}")
            return []
        except Exception as e:
            logging.exception(f"Error loading roadmap: {e}")
            return []

    def list_files(self):
        pass