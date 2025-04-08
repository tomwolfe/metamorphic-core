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
                # Regex to parse ROADMAP.md entries with robust spacing and newline handling
                task_pattern = re.compile(
                    r"""
                    \*\s+\*\*Task ID\*\*\:\s*(?P<task_id>[^\n]+?)\n  # Match "Task ID" followed by any characters until newline (non-greedy)
                    \s*\*\s+\*\*Priority\*\*\:\s*(?P<priority>[^\n]+?)\n # Match "Priority" followed by any characters until newline (non-greedy)
                    \s*\*\s+\*\*Task Name\*\*\:\s*(?P<task_name>.+?)\n      # Match "Task Name" followed by any characters (including newlines), until newline (non-greedy)
                    (?:                                                       # Non-capturing group for optional "Status"
                        \s*\*\s+\*\*Status\*\*\:\s*(?P<status>.+?)\n         # Match "Status" followed by any characters (including newlines) until newline (non-greedy)
                    )?                                                        # Make the entire "Status" section optional
                    """,
                    re.MULTILINE | re.DOTALL | re.VERBOSE
                )

                for match in task_pattern.finditer(content):
                    if match:
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
            logging.error(f"Error loading roadmap: {e}")
            return []