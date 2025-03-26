from flask import Blueprint, request, jsonify
from src.core.ethics.governance import EthicalGovernanceEngine
# Removed unused import: CodeReviewAgent
import os
import logging # Added logging
from jsonschema import ValidationError # Import validation error

ethical_bp = Blueprint('ethical', __name__)
logger = logging.getLogger(__name__) # Initialize logger

# Instantiate the engine once
ethical_governance_engine = EthicalGovernanceEngine()

# --- Default Policy Loading ---
# Determine the base directory of the project reliably
# Assuming this file is at src/api/routes/ethical_endpoints.py
# Go up 4 levels to reach the project root
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
DEFAULT_POLICY_PATH = os.path.join(project_root, 'policies', 'policy_bias_risk_strict.json')
logger.info(f"Default policy path determined as: {DEFAULT_POLICY_PATH}")

# Load the default policy at startup, handle potential errors
try:
    if not os.path.exists(DEFAULT_POLICY_PATH):
         logger.error(f"CRITICAL: Default policy file not found at {DEFAULT_POLICY_PATH}")
         # Depending on requirements, you might exit, use a fallback, or raise an exception
         # For now, log error and proceed (endpoint will fail later if policy needed)
         default_policy_config = None
    else:
         default_policy_config = ethical_governance_engine.load_policy_from_json(DEFAULT_POLICY_PATH)
         logger.info(f"Successfully loaded default policy: {default_policy_config.get('policy_name')}")
except (FileNotFoundError, json.JSONDecodeError, ValidationError, Exception) as e:
    logger.error(f"CRITICAL: Failed to load default policy '{DEFAULT_POLICY_PATH}': {e}")
    default_policy_config = None # Ensure it's None if loading fails

def get_policy_config(policy_name: str = None) -> dict:
    """
    Loads the specified policy or the default policy.
    For MVP, it primarily loads the default policy.
    """
    # MVP Simplification: Always use the pre-loaded default policy
    if default_policy_config is None:
         logger.error("Default policy was not loaded successfully at startup. Cannot proceed.")
         raise RuntimeError("Default ethical policy configuration is unavailable.") # Raise runtime error if default failed to load
    # Post-MVP: Add logic here to load different policies based on 'policy_name'
    # e.g., construct path, call engine.load_policy_from_json, handle errors
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
    try:
        data = request.get_json()
        if not data or 'code' not in data:
            logger.warning("Received request without 'code' field.")
            return jsonify({"status": "error", "message": "Missing 'code' field in request body"}), 400

        code = data['code']
        # For MVP, we use the default policy. Post-MVP could get policy name from request:
        # policy_name = data.get('policy_name')
        # current_policy = get_policy_config(policy_name)
        current_policy = get_policy_config() # Use default

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
            "code_quality": code_quality_results,
            "ethical_analysis": ethical_analysis_results, # Return the full results from the engine
            "generated_tests_placeholder": generated_tests_placeholder
        }

        # Log key results
        logger.info(f"Ethical analysis completed. Policy: '{current_policy.get('policy_name')}'. Overall Status: {overall_status}.")
        violation_details = {k: v['status'] for k, v in ethical_analysis_results.items() if isinstance(v, dict) and 'status' in v}
        logger.debug(f"Constraint Statuses: {violation_details}")


        return jsonify(response_payload), 200

    except RuntimeError as e:
         # Catch specific error if default policy failed to load
         logger.error(f"Runtime error in /analyze-ethical: {e}", exc_info=True)
         return jsonify({"status": "error", "message": str(e)}), 500
    except Exception as e:
        # Generic error handler for unexpected issues
        logger.error(f"Unexpected error in /analyze-ethical: {e}", exc_info=True)
        return jsonify({"status": "error", "message": "An unexpected internal server error occurred."}), 500