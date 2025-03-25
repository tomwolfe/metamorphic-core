from flask import Blueprint, request, jsonify
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine
import os

ethical_bp = Blueprint('ethical', __name__)

# code_review_agent = CodeReviewAgent() # <-- commented out for lazy instantiation in endpoint
# ethical_policy_engine = EthicalPolicyEngine() # <-- commented out for lazy instantiation in endpoint
ethical_governance_engine = EthicalGovernanceEngine() # Instantiate Engine

def load_default_policy():
    """Load the default policy from the policies directory"""
    policy_path = os.path.join(
        os.path.dirname(__file__),
        '..', '..', '..', 'policies', 'policy_bias_risk_strict.json'
    )
    return ethical_governance_engine.load_policy_from_json(policy_path)


@ethical_bp.route('/health', methods=['GET']) # Added /health endpoint to blueprint as per LLM suggestion Option A
def health_check():
    return jsonify({"status": "ready"}), 200

@ethical_bp.route('/analyze-ethical', methods=['POST'])
def genesis_ethical_analysis_endpoint():
    try:
        code = request.get_json().get('code')
        if not code: # Added code check as per LLM suggestion
            return jsonify({"error": "No code provided"}), 400 # Return 400 for no code

        default_policy = load_default_policy()
        ethical_analysis = ethical_governance_engine.enforce_policy(code, default_policy)

        return jsonify({
            "status": "success",
            "code_quality": {},  # Existing CodeReviewAgent output
            "ethical_analysis": ethical_analysis,
            "generated_tests_placeholder": {}  # Existing TestGenAgent output
        }), 200

    except Exception as e:
        return jsonify({
            "status": "error",
            "message": str(e)
        }), 500
