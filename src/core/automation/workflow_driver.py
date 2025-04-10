import logging
import os
import json

class WorkflowDriver:
    def __init__(self):
        pass

    def __repr__(self):
        return f"<{self.__class__.__name__} instance>"

    def load_roadmap(self, roadmap_path):
        tasks = []
        max_file_size = 1024 * 10  # 10KB limit
        try:
            if not roadmap_path.endswith(".json"):
                logging.error("ROADMAP must be a .json file")
                return []

            if os.path.getsize(roadmap_path) > max_file_size:
                logging.error(f"ROADMAP.json file exceeds maximum allowed size of {max_file_size} bytes.")
                return []

            with open(roadmap_path, 'r') as f:
                data = json.load(f)
                tasks = data.get("tasks", [])  # Added check to extract tasks

            # Basic validation to make sure tasks are a list.
            if not isinstance(tasks, list):
                logging.error("ROADMAP.json must contain a 'tasks' key with a list value.")
                return []

            # Basic validation and sanitization to ensure only expected values are in the data
            validated_tasks = []
            for task in tasks:
                if not isinstance(task, dict):
                    logging.warning("Skipping non-dictionary task entry.")
                    continue

                validated_task = {
                    "task_id": str(task.get("task_id", "")),  # Convert to string
                    "priority": str(task.get("priority", "")),  # Convert to string
                    "task_name": str(task.get("task_name", "")),  # Convert to string
                    "status": str(task.get("status", "")),  # Convert to string
                    "description": str(task.get("description", ""))
                }

                # Check for long task names, as before
                if len(validated_task['task_name']) > 150:
                    logging.warning(f"Task Name '{validated_task['task_name'][:50]}...' exceeds 150 characters, skipping task.")
                    continue

                # Basic XSS protection for task name and description
                validated_task['task_name'] = validated_task['task_name'].replace("<script>", "<script>").replace("</script>", "</script>")
                validated_task['description'] = validated_task['description'].replace("<script>", "<script>").replace("</script>", "</script>")

                validated_tasks.append(validated_task)

            return validated_tasks

        except FileNotFoundError:
            logging.error(f"ROADMAP.json file not found at path: {roadmap_path}")
            return []
        except json.JSONDecodeError as e:
            logging.error(f"Error decoding JSON from {roadmap_path}: {e}")
            return []
        except Exception as e:
            logging.exception(f"Error loading roadmap: {e}")
            return []

    def list_files(self):
        pass