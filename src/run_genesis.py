# src/run_genesis.py
"""
Script to execute the WorkflowDriver and display output.
"""
import logging
from src.core.automation.workflow_driver import WorkflowDriver
import os

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def main():
    """
    Main function to instantiate and run the WorkflowDriver.
    """
    driver = WorkflowDriver()
    roadmap_path = "ROADMAP.md"  # Define the roadmap path

    logger.info("Loading Roadmap...")
    try:
        tasks = driver.load_roadmap(roadmap_path)
        logger.info("Roadmap Tasks: %s", tasks)
    except FileNotFoundError:
        logger.error(f"Roadmap file not found at path: {roadmap_path}")
        return
    except Exception as e:
        logger.exception(f"Error loading roadmap: {e}")
        return

    logger.info("Listing Files...")
    try:
        files = driver.list_files()
        logger.info("Files: %s", files)
    except Exception as e:
        logger.exception(f"Error listing files: {e}")

if __name__ == "__main__":
    main()
