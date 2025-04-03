# src/api/routes/ethical_endpoints.py
from flask import Blueprint, request, jsonify
from src.core.ethics.governance import EthicalGovernanceEngine
from src.core.agents.code_review_agent import CodeReviewAgent # <--- IMPORT Agent
import os
import logging
from jsonschema import ValidationError, SchemaError
import json
from typing import Optional

ethical_bp = Blueprint('ethical', __name__)
logger = logging.getLogger(__name__)

# Instantiate engines/agents once if stateless or thread-safe
ethical_governance_engine = EthicalGovernanceEngine()
code_review_agent = CodeReviewAgent() # <--- INSTANTIATE Agent

# --- Default Policy Loading ---
# (Keep existing default policy loading logic - unchanged)
DEFAULT_POLICY_FILENAME = 'policy_bias_risk_strict.json'
DEFAULT_POLICY_PATH = os.path.abspath(os.path.join('policies', DEFAULT_POLICY_FILENAME))
logger.info(f"Attempting to load default policy from: {DEFAULT_POLICY_PATH}")
try:
    if not os.path.exists(DEFAULT_POLICY_PATH):
         script_dir = os.path.dirname(__file__)
         alt_path = os.path.abspath(os.path.join(script_dir, '..', '..', '..', 'policies', DEFAULT_POLICY_FILENAME))
         logger.warning(f"Default policy not found at {DEFAULT_POLICY_PATH}, trying alternative path: {alt_path}")
         if not os.path.exists(alt_path):
              logger.error(f"CRITICAL: Default policy file not found at {DEFAULT_POLICY_PATH} or {alt_path}")
              default_policy_config = None
         else:
              DEFAULT_POLICY_PATH = alt_path
              default_policy_config = ethical_governance_engine.load_policy_from_json(DEFAULT_POLICY_PATH)
              logger.info(f"Successfully loaded default policy from alternative path: {DEFAULT_POLICY_PATH} ({default_policy_config.get('policy_name')})")
    else:
         default_policy_config = ethical_governance_engine.load_policy_from_json(DEFAULT_POLICY_PATH)
         logger.info(f"Successfully loaded default policy: {DEFAULT_POLICY_PATH} ({default_policy_config.get('policy_name')})")
except (FileNotFoundError, json.JSONDecodeError, ValidationError, SchemaError, Exception) as e:
    logger.error(f"CRITICAL: Failed to load default policy '{DEFAULT_POLICY_PATH}': {e}", exc_info=True)
    default_policy_config = None

def get_policy_config(policy_name: str = None) -> Optional[dict]:
    # (Keep existing get_policy_config logic - unchanged)
    if policy_name:
        if not policy_name.replace('_', '').isalnum():
             logger.warning(f"Invalid characters in requested policy name: {policy_name}")
             raise ValueError(f"Invalid policy name format: {policy_name}")
        requested_policy_filename = f"{policy_name}.json"
        requested_policy_path = os.path.abspath(os.path.join('policies', requested_policy_filename))
        logger.info(f"Attempting to load requested policy: {requested_policy_path}")
        return ethical_governance_engine.load_policy_from_json(requested_policy_path)
    else:
        if default_policy_config is None:
            logger.error("Default policy was not loaded successfully at startup. Cannot proceed.")
            raise RuntimeError("Default ethical policy configuration is unavailable.")
        logger.debug(f"Using default policy: {default_policy_config.get('policy_name')}")
        return default_policy_config

@ethical_bp.route('/health', methods=['GET'])
def health_check():
    # (Keep existing health_check logic - unchanged)
    health_status = {"status": "ready"}
    if default_policy_config is None:
         health_status["status"] = "degraded"
         health_status["error"] = "Default ethical policy failed to load."
         return jsonify(health_status), 500
    return jsonify(health_status), 200

@ethical_bp.route('/analyze-ethical', methods=['POST'])
def genesis_ethical_analysis_endpoint():
    """
    Analyzes Python code for ethical considerations based on a configurable policy
    and performs basic code quality checks (Flake8).
    """
    current_policy = None
    try:
        data = request.get_json()
        if not data or 'code' not in data:
            logger.warning("Received request without 'code' field.")
            return jsonify({"status": "error", "message": "Missing 'code' field in request body"}), 400

        code = data['code']
        policy_name = data.get('policy_name')

        # --- Load Policy ---
        # (Keep existing policy loading logic - unchanged)
        try:
            current_policy = get_policy_config(policy_name)
        except FileNotFoundError:
             logger.warning(f"Requested policy '{policy_name}' not found.")
             return jsonify({"status": "error", "message": f"Policy '{policy_name}' not found."}), 404
        except (ValueError, json.JSONDecodeError, ValidationError, SchemaError) as e:
             logger.warning(f"Requested policy '{policy_name}' is invalid: {e}")
             return jsonify({"status": "error", "message": f"Policy '{policy_name}' is invalid: {e}"}), 400
        except RuntimeError as e:
             logger.error(f"Runtime error getting policy config: {e}", exc_info=True)
             return jsonify({"status": "error", "message": str(e)}), 500

        # --- Ethical Analysis ---
        # (Keep existing ethical analysis logic - unchanged)
        try:
            ethical_analysis_results = ethical_governance_engine.enforce_policy(code, current_policy)
        except Exception as e:
             logger.error(f"Error during ethical policy enforcement: {e}", exc_info=True)
             return jsonify({"status": "error", "message": "Internal error during ethical analysis."}), 500

        # --- Code Quality (Flake8 via CodeReviewAgent) ---
        try:
            flake8_results = code_review_agent.analyze_python(code)

            # Basic check if the agent returned a dictionary
            if not isinstance(flake8_results, dict):
                logger.error(f"CodeReviewAgent returned unexpected type: {type(flake8_results)}")
                raise TypeError("Code review agent did not return expected results format.")

            # Structure the results for the API response
            code_quality_results = {
                "output": flake8_results.get('output', ''),
                "issues_found": len(flake8_results.get('static_analysis', [])),
            }
            if 'error' in flake8_results:
                # Log the specific error from the agent for better debugging
                logger.error(f"CodeReviewAgent analysis failed: {flake8_results['error']}")
                code_quality_results["error"] = f"Flake8 analysis failed: {flake8_results['error']}"

        except Exception as e:
             # Catch potential TypeError from above or other unexpected agent errors
             logger.error(f"Error during code quality analysis execution: {e}", exc_info=True)
             code_quality_results = {
                 "output": "Error during Flake8 analysis.",
                 "issues_found": -1,
                 "error": f"Internal error during code quality check: {str(e)}"
             }

        # --- Test Generation (Placeholder/Integration Point) ---
        # (Keep existing placeholder - unchanged)
        generated_tests_placeholder = "import pytest\n# Placeholder tests - Integrate TestGenAgent"

        # --- Determine Overall Status ---
        # (Keep existing status logic - unchanged)
        overall_status = ethical_analysis_results.get("overall_status", "error")

        # --- Construct Response ---
        # (Keep existing response construction - unchanged)
        response_payload = {
            "status": overall_status,
            "requested_policy_name": current_policy.get('policy_name', 'Unknown'),
            "code_quality": code_quality_results,
            "ethical_analysis": ethical_analysis_results,
            "generated_tests_placeholder": generated_tests_placeholder
        }

        logger.info(f"Ethical analysis completed. Policy: '{current_policy.get('policy_name')}'. Overall Status: {overall_status}. Flake8 Issues: {code_quality_results.get('issues_found', 'N/A')}")
        violation_details = {k: v['status'] for k, v in ethical_analysis_results.items() if isinstance(v, dict) and 'status' in v}
        logger.debug(f"Constraint Statuses: {violation_details}")

        return jsonify(response_payload), 200

    except Exception as e:
        logger.error(f"Unexpected error in /analyze-ethical: {e}", exc_info=True)
        return jsonify({"status": "error", "message": "An unexpected internal server error occurred."}), 500