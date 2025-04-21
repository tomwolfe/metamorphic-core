# src/cli/main.py
"""
This module serves as the command-line interface (CLI) entry point for the Metamorphic Software Genesis Ecosystem.
It provides argument parsing with validation for roadmap files and output directories.
"""

import argparse
import os
import logging
import requests
import json
import sys
# Removed import of WorkflowDriver as it's no longer directly instantiated here
from src.core.automation.workflow_driver import Context # Keep Context import if needed elsewhere (currently not used in this file after changes)

# Configure logging for the CLI
# Check if handlers are already configured to avoid adding duplicates in environments like pytest
if not logging.root.handlers:
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Removed the placeholder logic for loading roadmap and selecting task

def _validate_roadmap_path(value):
    """Validate the provided roadmap file path.

    Args:
        value (str): Path to the roadmap file

    Returns:
        str: Validated  path if validation passes

    Raises:
        argparse.ArgumentTypeError: If path doesn't exist or isn't a file
    """
    if not os.path.exists(value):
        raise argparse.ArgumentTypeError(f"Roadmap file {value} does not exist")
    if not os.path.isfile(value):
        raise argparse.ArgumentTypeError(f"{value} is not a valid file")
    # Do not call abspath()
    return value


def _validate_output_dir(value):
    """Validate the provided output directory path.

    Args:
        value (str): Path to the output directory

    Returns:
        str: Validated path if validation passes

    Raises:
        argparse.ArgumentTypeError: If path doesn't exist or isn't a directory
    """
    if not os.path.exists(value):
        raise argparse.ArgumentTypeError(f"Output directory {value} does not exist")
    if not os.path.isdir(value):
        raise argparse.ArgumentTypeError(f"{value} is not a directory")
    # Do not call abspath()
    return value


def cli_entry_point():
    """
    Main entry point function for the CLI.

    Sets up the argument parser with roadmap and output directory arguments,
    handles validation, and calls the API to initiate the workflow.
    """
    parser = argparse.ArgumentParser(
        description="Metamorphic Software Genesis Ecosystem CLI",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    # Version argument
    parser.add_argument(
        "--version",
        action="version",
        version="Metamorphic CLI v0.1.0-alpha",
        help="Show the version number and exit",
    )

    # Roadmap file argument
    parser.add_argument(
        "--roadmap",
        type=_validate_roadmap_path,
        default="ROADMAP.json",
        help="Path to the roadmap JSON file",
    )

    # Output directory argument
    parser.add_argument(
        "--output-dir",
        type=_validate_output_dir,
        default="./output",
        help="Path to the output directory",
    )

    args = parser.parse_args()

    # Display validated paths for verification
    print(f"Using roadmap: {args.roadmap}")
    print(f"Using output directory: {args.output_dir}")

    # --- Logic to call the API endpoint ---
    # Note: API host/port is hardcoded for now. Future iterations may make this configurable.
    api_url = "http://127.0.0.1:5000/genesis/drive_workflow"
    payload = {
        "roadmap_path": args.roadmap, #Pass the raw paths, not abspath()
        "output_dir": args.output_dir #Pass the raw paths, not abspath()
    }

    # Security Note: The CLI validates the existence and type of paths using _validate_roadmap_path
    # and _validate_output_dir. However, these checks do not prevent path traversal
    # relative to the API server's working directory. Crucially, the API endpoint
    # `/genesis/drive_workflow` MUST perform its own robust path validation (e.g.,
    # using _is_safe_path) before using these paths in any file operations to prevent
    # path traversal vulnerabilities. The CLI relies on the API's validation for the
    # final security check against malicious paths.

    logger.info(f"Calling API to initiate workflow at {api_url}...")

    try:
        response = requests.post(api_url, json=payload)

        if response.status_code == 200:
            try:
                response_json = response.json()
                logger.info(f"Workflow initiated successfully via API. Status: {response_json.get('status')}, Message: {response_json.get('message')}")
            except json.JSONDecodeError:
                 # Handle case where API returns 200 but non-JSON (unexpected but possible)
                 logger.info(f"Workflow initiated successfully, but API returned non-JSON response. Status Code: 200. Response: {response.text[:200]}...")
        else:
            try:
                # Attempt to get JSON error message for non-200 responses
                response_json = response.json()
                error_message = response_json.get('message', 'No specific error message provided in JSON.')
            except json.JSONDecodeError:
                # Fallback to raw text if response is non-JSON
                error_message = f"API returned non-JSON response (Status {response.status_code}): {response.text[:200]}..."

            logger.error(f"API returned error status code: {response.status_code}. Message: {error_message}")
            sys.exit(1) # Exit with error code

    except requests.exceptions.ConnectionError as e:
        logger.error(f"Failed to connect to API endpoint {api_url}: {e}")
        logger.error("Please ensure the Flask API server is running.")
        sys.exit(1) # Exit with error code
    except requests.exceptions.RequestException as e:
        # Catch other requests exceptions (timeout, etc.)
        logger.error(f"An error occurred during API request to {api_url}: {e}")
        sys.exit(1) # Exit with error code
    except Exception as e:
        # Catch any other unexpected exceptions during the API call process
        logger.error(f"An unexpected error occurred: {e}", exc_info=True)
        sys.exit(1) # Exit with error code


if __name__ == "__main__":
    cli_entry_point()