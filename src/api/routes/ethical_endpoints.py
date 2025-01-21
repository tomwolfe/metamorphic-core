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
            # You might want to expose some quantum state info if needed
            # "quantum_state": quantum_core.analyze_quantum_state(hash(code))
        }), 403

    return jsonify({"status": "APPROVED", "analysis": analysis_result})
