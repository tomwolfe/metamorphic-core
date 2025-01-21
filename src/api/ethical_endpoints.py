# api/ethical_endpoints.py
from flask import Blueprint, request, jsonify
from .quantum_ethical_core import QuantumEthicalValidator

ethical_bp = Blueprint('ethical', __name__)
validator = QuantumEthicalValidator()

@ethical_bp.route('/analyze', methods=['POST'])
def ethical_analysis():
    code = request.json.get('code')
    if not code:
        return jsonify({"error": "No code provided"}), 400
    
    analysis = validator.validate_decision(code)
    
    # Quantum decision threshold
    if analysis['bias_risk'] > 0.25 or analysis['safety_risk'] > 0.3:
        return jsonify({
            "status": "REJECTED",
            "analysis": analysis,
            "quantum_state": validator._create_ethical_circuit().qasm()
        }), 403
    
    return jsonify({"status": "APPROVED", "analysis": analysis})
