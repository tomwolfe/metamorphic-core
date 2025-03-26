from flask import Blueprint, request, jsonify
from src.core.ethics.governance import EthicalGovernanceEngine
# Removed unused import: CodeReviewAgent
import os
import logging # Added logging
from jsonschema import ValidationError, SchemaError # Import validation error AND SchemaError
import json # Need json for JSONDecodeError
from typing import Optional # Import Optional

ethical_bp = Blueprint('ethical', __name__)
logger = logging.getLogger(__name__) # Initialize logger

# Instantiate the engine once
ethical_governance_engine = EthicalGovernanceEngine()

# --- Default Policy Loading ---
# FIX: Calculate path relative to the container's WORKDIR (/app)
# The 'policies' directory is directly under /app after the COPY instruction
DEFAULT_POLICY_FILENAME = 'policy_bias_risk_strict.json'
# Assume WORKDIR is /app, so policies is directly under it
DEFAULT_POLICY_PATH = os.path.abspath(os.path.join('policies', DEFAULT_POLICY_FILENAME))

logger.info(f"Attempting to load default policy from: {DEFAULT_POLICY_PATH}")

# Load the default policy at startup, handle potential errors
try:
    if not os.path.exists(DEFAULT_POLICY_PATH):
         # If not found relative to WORKDIR, try relative to the script's dir (less ideal in Docker)
         script_dir = os.path.dirname(__file__)
         alt_path = os.path.abspath(os.path.join(script_dir, '..', '..', '..', 'policies', DEFAULT_POLICY_FILENAME))
         logger.warning(f"Default policy not found at {DEFAULT_POLICY_PATH}, trying alternative path: {alt_path}")
         if not os.path.exists(alt_path):
              logger.error(f"CRITICAL: Default policy file not found at {DEFAULT_POLICY_PATH} or {alt_path}")
              default_policy_config = None
         else:
              DEFAULT_POLICY_PATH = alt_path # Use the alternative path if it exists
              default_policy_config = ethical_governance_engine.load_policy_from_json(DEFAULT_POLICY_PATH)
              logger.info(f"Successfully loaded default policy from alternative path: {DEFAULT_POLICY_PATH} ({default_policy_config.get('policy_name')})")

    else:
         default_policy_config = ethical_governance_engine.load_policy_from_json(DEFAULT_POLICY_PATH)
         logger.info(f"Successfully loaded default policy: {DEFAULT_POLICY_PATH} ({default_policy_config.get('policy_name')})")

except (FileNotFoundError, json.JSONDecodeError, ValidationError, SchemaError, Exception) as e:
    logger.error(f"CRITICAL: Failed to load default policy '{DEFAULT_POLICY_PATH}': {e}", exc_info=True) # Add exc_info for more details
    default_policy_config = None # Ensure it's None if loading fails

def get_policy_config(policy_name: str = None) -> Optional[dict]:
    """
    Loads the specified policy or the default policy.

    Args:
        policy_name: The name of the policy file (without .json extension).
                     If None, loads the default policy.

    Returns:
        The loaded policy dictionary, or None if the requested policy fails to load.

    Raises:
        RuntimeError: If the default policy failed to load at startup and is requested.
        FileNotFoundError: If the requested policy file is not found.
        ValueError: If the policy_name contains invalid characters.
        json.JSONDecodeError: If the requested policy file contains invalid JSON.
        ValidationError: If the requested policy file fails schema validation.
        SchemaError: If the schema itself is invalid during validation.
        Exception: For other unexpected errors during loading/validation.
    """
    if policy_name:
        # Construct path for the requested policy
        # Basic sanitization: allow only alphanumeric and underscores
        if not policy_name.replace('_', '').isalnum():
             logger.warning(f"Invalid characters in requested policy name: {policy_name}")
             raise ValueError(f"Invalid policy name format: {policy_name}") # Raise ValueError for invalid format
        requested_policy_filename = f"{policy_name}.json"
        requested_policy_path = os.path.abspath(os.path.join('policies', requested_policy_filename))
        logger.info(f"Attempting to load requested policy: {requested_policy_path}")
        # load_policy_from_json will raise appropriate errors if loading fails
        return ethical_governance_engine.load_policy_from_json(requested_policy_path)
    else:
        # Use the pre-loaded default policy
        if default_policy_config is None:
            logger.error("Default policy was not loaded successfully at startup. Cannot proceed.")
            raise RuntimeError("Default ethical policy configuration is unavailable.")
        logger.debug(f"Using default policy: {default_policy_config.get('policy_name')}")
        return default_policy_config

@ethical_bp.route('/health', methods=['GET'])
def health_check():
    # Add a check for default policy loading status
    health_status = {"status": "ready"}
    if default_policy_config is None:
         health_status["status"] = "degraded"
         health_status["error"] = "Default ethical policy failed to load."
         return jsonify(health_status), 500 # Return 500 if essential config missing
    return jsonify(health_status), 200

@ethical_bp.route('/analyze-ethical', methods=['POST'])
def genesis_ethical_analysis_endpoint():
    """
    Analyzes Python code for ethical considerations based on a configurable policy
    and performs basic code quality checks (Flake8).
    """
    current_policy = None # Initialize
    try:
        data = request.get_json()
        if not data or 'code' not in data:
            logger.warning("Received request without 'code' field.")
            return jsonify({"status": "error", "message": "Missing 'code' field in request body"}), 400

        code = data['code']
        policy_name = data.get('policy_name') # Get requested policy name (optional)

        # --- Load Policy ---
        try:
            current_policy = get_policy_config(policy_name)
        except FileNotFoundError:
             logger.warning(f"Requested policy '{policy_name}' not found.")
             return jsonify({"status": "error", "message": f"Policy '{policy_name}' not found."}), 404 # Not Found
        except (ValueError, json.JSONDecodeError, ValidationError, SchemaError) as e:
             logger.warning(f"Requested policy '{policy_name}' is invalid: {e}")
             return jsonify({"status": "error", "message": f"Policy '{policy_name}' is invalid: {e}"}), 400 # Bad Request
        except RuntimeError as e: # Catch if default policy failed startup and wasn't requested
             logger.error(f"Runtime error getting policy config: {e}", exc_info=True)
             return jsonify({"status": "error", "message": str(e)}), 500

        # --- Ethical Analysis ---
        try:
            ethical_analysis_results = ethical_governance_engine.enforce_policy(code, current_policy)
        except Exception as e:
             logger.error(f"Error during ethical policy enforcement: {e}", exc_info=True)
             return jsonify({"status": "error", "message": "Internal error during ethical analysis."}), 500

        # --- Code Quality (Placeholder/Integration Point) ---
        # TODO: Integrate CodeReviewAgent call here post-MVP or if needed for MVP refinement
        code_quality_results = {
             "output": "Flake8 analysis placeholder - Integrate CodeReviewAgent",
             "static_analysis": []
        }

        # --- Test Generation (Placeholder/Integration Point) ---
        # TODO: Integrate TestGenAgent call here post-MVP or if needed for MVP refinement
        generated_tests_placeholder = "import pytest\n# Placeholder tests - Integrate TestGenAgent"


        # --- Determine Overall Status ---
        # Status is 'rejected' if any ethical constraint was violated, otherwise 'approved'.
        overall_status = ethical_analysis_results.get("overall_status", "error") # Get status from engine results

        # --- Construct Response ---
        response_payload = {
            "status": overall_status, # Use the status determined by the engine
            "requested_policy_name": current_policy.get('policy_name', 'Unknown'), # Add policy name used
            "code_quality": code_quality_results,
            "ethical_analysis": ethical_analysis_results, # Return the full results from the engine
            "generated_tests_placeholder": generated_tests_placeholder
        }

        # Log key results
        logger.info(f"Ethical analysis completed. Policy: '{current_policy.get('policy_name')}'. Overall Status: {overall_status}.")
        violation_details = {k: v['status'] for k, v in ethical_analysis_results.items() if isinstance(v, dict) and 'status' in v}
        logger.debug(f"Constraint Statuses: {violation_details}")


        return jsonify(response_payload), 200

    except Exception as e:
        # Generic error handler for unexpected issues
        logger.error(f"Unexpected error in /analyze-ethical: {e}", exc_info=True)
        # Ensure a response is always sent
        return jsonify({"status": "error", "message": "An unexpected internal server error occurred."}), 500