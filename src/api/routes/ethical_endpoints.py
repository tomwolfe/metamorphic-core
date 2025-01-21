# api/ethical_endpoints.py
from flask import Blueprint, request, jsonify
from src.core.ethics.governance import QuantumEthicalValidator  # Absolute import
from src.core.quantum.ethical_validation import EthicalQuantumCore  # New import

ethical_bp = Blueprint('ethical', __name__)
validator = QuantumEthicalValidator()
quantum_core = EthicalQuantumCore()  # Now using correct class

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
