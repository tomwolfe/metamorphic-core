# dev_run.py
import subprocess
import sys
import argparse
import os
import logging
import requests # Add import
import time     # Add import

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def dev_run_workflow():
    """
    Restarts the metamorphic-core Docker service and initiates the workflow via the CLI.
    """
    parser = argparse.ArgumentParser(
        description="Metamorphic Software Genesis Ecosystem Development Runner",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    parser.add_argument(
        "--roadmap",
        type=str, # Accept string, validation happens downstream in CLI/API
        default="ROADMAP.json",
        help="Path to the roadmap JSON file (relative to project root)",
    )

    parser.add_argument(
        "--output-dir",
        type=str, # Accept string, validation happens downstream in CLI/API
        default="./output",
        help="Path to the output directory (relative to project root)",
    )

    args = parser.parse_args()

    logger.info("Attempting to restart 'metamorphic-core' Docker service...")
    try:
        # Use subprocess.run with a list for safety against shell injection
        # Capture output for logging
        restart_process = subprocess.run(
            ["docker-compose", "restart", "metamorphic-core"],
            capture_output=True,
            text=True,
            check=False # Do not raise CalledProcessError on non-zero exit
        )
        logger.info(f"Docker Compose Restart STDOUT:\n{restart_process.stdout}")
        if restart_process.stderr:
             logger.warning(f"Docker Compose Restart STDERR:\n{restart_process.stderr}")

        if restart_process.returncode != 0:
            logger.error(f"Docker Compose Restart failed with exit code {restart_process.returncode}.")
            logger.error("Please ensure Docker is running and 'metamorphic-core' service is defined in docker-compose.yml.")
            sys.exit(1) # Exit if docker-compose restart fails

        logger.info("'metamorphic-core' service restarted successfully.")

        # Health check loop
        health_url = "http://localhost:5000/genesis/health" # Assuming default port
        max_attempts = 30 # Try for 60 seconds
        logger.info(f"Attempting to contact API server at {health_url}...")
        for attempt in range(max_attempts):
            try:
                response = requests.get(health_url, timeout=2)
                if response.status_code == 200 and response.json().get("status") == "ready":
                    logger.info("API server is healthy and ready.")
                    break
                else:
                    logger.warning(f"API health check attempt {attempt+1}/{max_attempts} failed: Status {response.status_code}, Response: {response.text[:100]}")
            except requests.exceptions.RequestException as e:
                logger.warning(f"API health check attempt {attempt+1}/{max_attempts} failed: {e}")

            if attempt == max_attempts - 1:
                logger.error("API server did not become healthy after multiple attempts. Exiting.")
                sys.exit(1) # Exit if API server is not healthy
            time.sleep(2) # Wait before retrying


    except FileNotFoundError:
        logger.error("Error: 'docker-compose' command not found.")
        logger.error("Please ensure Docker Compose is installed and in your system's PATH.")
        sys.exit(1) # Exit if docker-compose command is not found
    except Exception as e:
        logger.error(f"An unexpected error occurred during Docker Compose restart: {e}", exc_info=True)
        sys.exit(1) # Exit on other unexpected errors

    logger.info(f"Initiating workflow via CLI with roadmap='{args.roadmap}' and output-dir='{args.output_dir}'...")
    try:
        # Use subprocess.run with a list for safety against shell injection
        # Pass arguments directly to the CLI script
        cli_command = [
            sys.executable, # Use sys.executable for robustness
            "src/cli/main.py",
            "--roadmap", args.roadmap,
            "--output-dir", args.output_dir
        ]

        # --- FIX START ---
        # Set PYTHONPATH for the subprocess
        # Copy the current environment variables
        env = os.environ.copy()
        # Set or update PYTHONPATH to include the 'src' directory relative to the current working directory
        # This assumes dev_run.py is run from the project root.
        # If PYTHONPATH already exists, prepend 'src' to it.
        env['PYTHONPATH'] = 'src' + os.pathsep + env.get('PYTHONPATH', '')
        # --- FIX END ---

        cli_process = subprocess.run(
            cli_command,
            cwd=os.getcwd(), # Ensure running from project root
            capture_output=True,
            text=True,
            check=False, # Do not raise CalledProcessError on non-zero exit
            env=env # --- Apply the modified environment ---
        )
        logger.info(f"CLI Execution STDOUT:\n{cli_process.stdout}")
        if cli_process.stderr:
             logger.warning(f"CLI Execution STDERR:\n{cli_process.stderr}")


        if cli_process.returncode != 0:
            logger.error(f"CLI execution failed with exit code {cli_process.returncode}.")
            # The CLI itself logs detailed errors from the API call, so no need to repeat here.
            sys.exit(1) # Exit if CLI execution fails

        logger.info("Workflow initiated successfully via CLI.")

    except FileNotFoundError:
        logger.error("Error: 'src/cli/main.py' script not found.")
        logger.error("Please ensure you are running this script from the project root directory.")
        sys.exit(1) # Exit if CLI script is not found
    except Exception as e:
        logger.error(f"An unexpected error occurred during CLI execution: {e}", exc_info=True)
        sys.exit(1) # Exit on other unexpected errors

    logger.info("Development workflow script finished.")
    sys.exit(0) # Exit with success code

if __name__ == "__main__":
    dev_run_workflow()