from flask import Blueprint, request, jsonify
from src.core.ethics.governance import QuantumEthicalValidator
from src.core.quantum.ethical_validation import EthicalQuantumCore

ethical_bp = Blueprint('ethical', __name__)
validator = QuantumEthicalValidator()
quantum_core = EthicalQuantumCore()

@ethical_bp.route('/analyze', methods=['POST'])
def ethical_analysis():
    code = request.json.get('code')
    if not code:
        return jsonify({"error": "No code provided"}), 400

    # Using the QuantumEthicalValidator for the main validation
    analysis_result = validator.validate_code(code)

    if not analysis_result['approved']:
        return jsonify({
            "status": "REJECTED",
            "analysis": analysis_result,
            "quantum_state": quantum_core.analyze_quantum_state(hash(code))
        }), 403

    return jsonify({"status": "APPROVED", "analysis": analysis_result})

@ethical_bp.route('/audit/<state_id>', methods=['GET'])
def get_audit_trail(state_id: str):
    """Retrieve complete audit trail with quantum state"""
    try:
        # Load ethical audit
        with open(f"ethical_audits/{state_id}.json") as f:
            audit_data = json.load(f)

        # Load quantum state
        with open(f"quantum_states/{state_id}.json") as f:
            quantum_state = json.load(f)

        return jsonify({
            "audit": audit_data,
            "quantum_state": quantum_state
        })
    except FileNotFoundError:
        return jsonify({"error": "Audit trail not found"}), 404
