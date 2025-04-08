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

            # Regex to match individual task entries, accounts for spacing
            task_pattern = re.compile(
                r"\*\s+\*\*Task ID\*\*\:\s*(?P<task_id>.*?)\n"
                r"\s*\*\s+\*\*Priority\*\*\:\s*(?P<priority>.*?)\n"
                r"\s*\*\s+\*\*Task Name\*\*\:\s*(?P<task_name>.*?)\n"
                r"(?:\s*\*\s+\*\*Status\*\*\:\s*(?P<status>.*?))?",
                re.DOTALL
            )

            # Find all matches of the task pattern
            matches = task_pattern.finditer(content)

            for match in matches:
                task = {}
                task_id = match.group("task_id").strip() if match.group("task_id") else ""
                priority = match.group("priority").strip() if match.group("priority") else ""
                task_name = match.group("task_name").strip() if match.group("task_name") else ""
                status = match.group("status").strip() if match.group("status") else ""

                if len(task_name) > 150:
                    logging.warning(f"Task Name '{task_name[:50]}...' exceeds 150 characters, skipping task.")
                    continue

                task['task_id'] = task_id
                task['priority'] = priority
                task['task_name'] = task_name
                task['status'] = status
                tasks.append(task)

            return tasks

        except FileNotFoundError:
            logging.error(f"ROADMAP.md file not found at path: {roadmap_path}")
            return []
        except Exception as e:
            logging.exception(f"Error loading roadmap: {e}")
            return []

    def list_files(self):
        return None