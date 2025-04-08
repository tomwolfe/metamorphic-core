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
        try:
            with open(roadmap_path, 'r') as f:
                content = f.read()

                # Corrected Regex: Simplified and made more robust for variations in spacing and optional Status
                # This regex makes the 'Status' section optional while extracting other task details.
                task_pattern = re.compile(
                    r"\*\s+\*\*Task ID\*\*\:\s*(?P<task_id>.*?)\n"  # Match "Task ID" and capture its value
                    r"\s*\*\s+\*\*Priority\*\*\:\s*(?P<priority>.*?)\n"  # Match "Priority" and capture its value
                    r"\s*\*\s+\*\*Task Name\*\*\:\s*(?P<task_name>.*?)\n"  # Match "Task Name" and capture its value
                    r"(?:\s*\*\s+\*\*Status\*\*\:\s*(?P<status>.*?)\n)?",  # Optionally match "Status" and capture its value
                    re.DOTALL  # Enable '.' to match any character, including newlines
                )

                for match in task_pattern.finditer(content):
                    if match:
                        task = match.groupdict()
                        # Strip whitespace and handle missing 'status' gracefully using a conditional expression
                        tasks.append({k: v.strip() if v else "" for k, v in task.items()})
                return tasks

        except FileNotFoundError:
            logging.error(f"ROADMAP.md file not found at path: {roadmap_path}")
            return []
        except Exception as e:
            logging.exception(f"Error loading roadmap: {e}") # Changed logging.error to logging.exception to print trace
            return []

    def list_files(self):
        return []