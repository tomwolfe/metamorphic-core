# scripts/generate_roadmap_md.py
import json

def generate_roadmap_md(json_path="ROADMAP.json", md_path="ROADMAP.md"):
    try:
        with open(json_path, 'r') as f:
            tasks = json.load(f)

        with open(md_path, 'w') as md_file:
            md_file.write("# Development Roadmap\n\n")
            for task in tasks:
                md_file.write(f"*   **Task ID**: {task['task_id']}\n")
                md_file.write(f"    *   **Priority**: {task['priority']}\n")
                md_file.write(f"    *   **Task Name**: {task['task_name']}\n")
                md_file.write(f"    *   **Status**: {task['status']}\n\n") # Leave the space in the string for markdown parsing
        print(f"Successfully generated {md_path} from {json_path}")

    except FileNotFoundError:
        print(f"Error: {json_path} not found.")
    except json.JSONDecodeError as e:
        print(f"Error decoding JSON: {e}")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    generate_roadmap_md()
