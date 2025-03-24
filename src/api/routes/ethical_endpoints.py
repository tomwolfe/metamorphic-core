from flask import Blueprint, request, jsonify
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine

ethical_bp = Blueprint('ethical', __name__)

# code_review_agent = CodeReviewAgent() # <-- commented out for lazy instantiation in endpoint
# ethical_policy_engine = EthicalPolicyEngine() # <-- commented out for lazy instantiation in endpoint


@ethical_bp.route('/health', methods=['GET']) # Added /health endpoint to blueprint as per LLM suggestion Option A
def health_check():
    return jsonify({"status": "ready"}), 200

@ethical_bp.route('/analyze-ethical', methods=['POST'])
def genesis_ethical_analysis_endpoint():
    code = request.get_json().get('code')
    if not code: # Added code check as per LLM suggestion
        return jsonify({"error": "No code provided"}), 400 # Return 400 for no code
    return jsonify({"status": "working"}) # Return 200 for valid request, further logic to be added in later weeks