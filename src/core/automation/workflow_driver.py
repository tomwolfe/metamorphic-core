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
                    r'\*\s+\*\*Task ID\*\*\:\s*(?P<task_id>[^\n]+?)\n'
                    r'(?P<details>(?:.*\n)*?)'  # Capture all lines until next task
                    r'(?=\*\s+\*\*Task ID\*\*|\Z)',  # Lookahead for next task or end
                    re.DOTALL
                )
                for match in task_pattern.finditer(content):
                    task_id = match.group("task_id").strip()
                    details = match.group("details")
                    
                    priority = ""
                    task_name = ""
                    status = ""
                    
                    lines = [line.strip() for line in details.split('\n') if line.strip()]
                    for line in lines:
                        if line.startswith('* **Priority**:'):
                            priority = line.split(':', 1)[1].strip()
                        elif line.startswith('* **Task Name**:'):
                            task_name = line.split(':', 1)[1].strip()
                        elif line.startswith('* **Status**:'):
                            status = line.split(':', 1)[1].strip()
                    
                    tasks.append({
                        "task_id": task_id,
                        "priority": priority,
                        "task_name": task_name,
                        "status": status,
                    })
                return tasks
        except FileNotFoundError:
            logging.error(f"ROADMAP.md file not found at path: {roadmap_path}")
            return []
        except Exception as e:
            logging.exception(f"Error loading or parsing ROADMAP.md: {e}")
            return []