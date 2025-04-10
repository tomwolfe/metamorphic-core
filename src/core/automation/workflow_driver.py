# src/core/automation/workflow_driver.py
import logging
import os
import json
import html
class Context:  # Added Context class
    def __init__(self, root_dir):
        self.root_dir = root_dir
class WorkflowDriver:
    def __init__(self, context): # Modified constructor
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
                logging.error("ROADMAP.json must contain a 'tasks' list")
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
                description = html.escape(task.get('description', '').strip())
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
        entries = os.listdir(self.context.root_dir)
        result = []
        for entry in entries:
            full_path = os.path.join(self.context.root_dir, entry)
            if os.path.isfile(full_path):
                result.append({'name': entry, 'status': 'file'})
            elif os.path.isdir(full_path):
                result.append({'name': entry, 'status': 'directory'})
        return result