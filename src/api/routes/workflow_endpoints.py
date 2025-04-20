# src/api/routes/workflow_endpoints.py
from flask import Blueprint, request, jsonify
import logging
import os
from src.core.automation.workflow_driver import WorkflowDriver, Context
from pathlib import Path # Import Path for robust path validation
import re # Import re for path validation regex
from werkzeug.exceptions import BadRequest # Import BadRequest explicitly

workflow_bp = Blueprint('workflow', __name__)
logger = logging.getLogger(__name__)

# Basic path validation regex - allows alphanumeric, underscores, hyphens, dots, forward slashes
# Prevents '..', leading/trailing slashes, and absolute paths starting with /
# Note: This is a simplified example, more robust validation might be needed depending on requirements
# A better approach is to resolve paths relative to a known safe base directory and check if the result is within that base.
# Let's adapt the validation logic from _write_output_file in workflow_driver.py
def _is_safe_path(base_path: str, requested_path: str) -> bool:
    """Validates that the requested path resolves safely within the base path."""
    if not requested_path:
        return False
    try:
        # Resolve the requested path relative to the base path
        full_requested_path = os.path.join(base_path, requested_path)
        resolved_path = Path(full_requested_path).resolve()
        resolved_base_path = Path(base_path).resolve()

        # Check if the resolved path starts with the resolved base path
        # This prevents '..' traversal and absolute paths
        return str(resolved_path).startswith(str(resolved_base_path))
    except Exception as e:
        logger.error(f"Path validation failed for {requested_path} relative to {base_path}: {e}", exc_info=True)
        return False


@workflow_bp.route('/drive_workflow', methods=['POST'])
def drive_workflow_endpoint():
    """
    API endpoint to initiate the WorkflowDriver's autonomous loop.
    """
    logger.info("Received request to /genesis/drive_workflow")
    # Do NOT wrap request.get_json() in the main try block
    # Let Flask handle BadRequest for invalid JSON
    data = request.get_json() # This can raise BadRequest

    try:
        if not data:
            logger.warning("Received empty request body.")
            return jsonify({"status": "error", "message": "Request body must be JSON"}), 400

        roadmap_path = data.get('roadmap_path')
        output_dir = data.get('output_dir')

        if not isinstance(roadmap_path, str) or not roadmap_path:
            logger.warning("Missing or invalid 'roadmap_path' in request.")
            return jsonify({"status": "error", "message": "Missing or invalid 'roadmap_path'"}), 400

        if not isinstance(output_dir, str) or not output_dir:
            logger.warning("Missing or invalid 'output_dir' in request.")
            return jsonify({"status": "error", "message": "Missing or invalid 'output_dir'"}), 400

        # Security: Validate paths to prevent traversal
        base_path = os.getcwd() # Use current working directory as the base
        if not _is_safe_path(base_path, roadmap_path):
             logger.warning(f"Path traversal attempt detected in roadmap_path: {roadmap_path}")
             return jsonify({"status": "error", "message": "Invalid 'roadmap_path' format or content"}), 400

        # Note: output_dir validation might need to ensure it's a directory path, not a file.
        # For now, basic safe path check is sufficient.
        if not _is_safe_path(base_path, output_dir):
             logger.warning(f"Path traversal attempt detected in output_dir: {output_dir}")
             return jsonify({"status": "error", "message": "Invalid 'output_dir' format or content"}), 400


        logger.info(f"Initiating workflow with roadmap: {roadmap_path}, output: {output_dir}")

        # Instantiate and start the driver
        # WorkflowDriver needs a Context object
        context = Context(base_path) # Use current working directory as base path for context
        driver = WorkflowDriver(context)

        # Call the new method to start the workflow
        # This should ideally run in a background thread or process for long-running tasks
        # For MVP, a simple call is acceptable, but note the potential for blocking
        # TODO: Implement background task execution for long-running workflows
        # --- CORRECTED: Add context argument ---
        driver.start_workflow(roadmap_path, output_dir, context) # Call the new method with context

        logger.info("Workflow initiation successful.")
        return jsonify({"status": "success", "message": "Workflow initiated"}), 200

    except Exception as e:
        # This block will now only catch exceptions *other than* BadRequest
        logger.error(f"Error initiating workflow: {e}", exc_info=True)
        return jsonify({"status": "error", "message": "Internal server error during workflow initiation"}), 500