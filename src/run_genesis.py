# src/run_genesis.py
from src.core.automation.workflow_driver import WorkflowDriver

if __name__ == "__main__":
    driver = WorkflowDriver()
    print("Loading Roadmap...")
    tasks = driver.load_roadmap("path/to/roadmap.md") # The path does not matter since the method currently has hardcoded output.
    print("Roadmap Tasks:", tasks)

    print("Listing Files...")
    files = driver.list_files()
    print("Files:", files) # Should print an empty list
