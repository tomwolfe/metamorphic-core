import logging
import os
import re

class WorkflowDriver:
    def __init__(self):
        pass

    def __repr__(self):
        return f"<{self.__class__.__name__} instance>"

    def load_roadmap(self, roadmap_path):
        try:
            with open(roadmap_path, 'r') as f:
                content = f.read()
                tasks = []
                task_pattern = re.compile(
                    r"""
                    ^\s*\*\s+\*\*Task ID\*\*\:\s*(?P<task_id>[^\n]+?)\n
                    \s*\*\s+\*\*Priority\*\*\:\s*(?P<priority>[^\n]+?)\n
                    \s*\*\s+\*\*Task Name\*\*\:\s*(?P<task_name>[^\n]+?)\n
                    (?:
                        \s*\*\s+\*\*Status\*\*\:\s*(?P<status>[^\n]+?)\n
                    )?
                    (?=
                        \n\s*\*|\Z
                    )
                    """,
                    re.DOTALL | re.MULTILINE | re.VERBOSE
                )
                for match in task_pattern.finditer(content):
                    task = {
                        "task_id": match.group("task_id").strip(),
                        "priority": match.group("priority").strip(),
                        "task_name": match.group("task_name").strip(),
                        "status": match.group("status").strip() if match.group("status") else "",
                    }
                    tasks.append(task)
                return tasks
        except FileNotFoundError:
            logging.error(f"ROADMAP.md file not found at path: {roadmap_path}")
            return []
        except Exception as e:
            logging.exception(f"Error loading or parsing ROADMAP.md: {e}")