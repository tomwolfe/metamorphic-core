import logging
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '.')))

from src.api.server import app  # Import Flask app
from src.core.llm_orchestration import LLMOrchestrator
from src.core.knowledge_graph import initialize_knowledge_graph

# Initialize logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def main():
    logger.info("Starting Metamorphic Genesis...")

    # Initialize Knowledge Graph
    kg = initialize_knowledge_graph()
    logger.info("Knowledge Graph initialized.")

    # Initialize LLM Orchestrator
    llm_orchestrator = LLMOrchestrator()
    logger.info("LLM Orchestrator initialized.")

    # Start Flask API server (moved to conditional block)
    if os.environ.get('RUN_FLASK_APP') == 'true': # Control via env var for flexibility
        logger.info("Starting Flask API server...")
        app.llm_orchestrator = llm_orchestrator # Inject LLM orchestrator
        app.run(debug=True, host="0.0.0.0", port=5000) # Run Flask app
    else:
        logger.info("Flask API server not started (RUN_FLASK_APP != 'true').")

    logger.info("Metamorphic Genesis initialization complete.")


if __name__ == "__main__":
    main()

    from src.core.automation.workflow_driver import WorkflowDriver # Import WorkflowDriver

    # Instantiate WorkflowDriver (after LLMOrchestrator)
    workflow_driver = WorkflowDriver(llm_orchestrator)

    # Example task execution (for testing)
    example_task_description = "Explain the purpose of the Knowledge Graph in the Metamorphic project."
    print(f"\n--- Running Workflow Driver Example Task: '{example_task_description}' ---")
    workflow_output = workflow_driver.run_workflow(example_task_description)
    print("\n--- Workflow Driver Output: ---")
    print(workflow_output)
