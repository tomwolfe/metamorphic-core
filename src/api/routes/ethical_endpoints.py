from flask import Blueprint, request, jsonify
from src.core.ethics.governance import QuantumEthicalValidator
from src.core.quantum.ethical_validation import EthicalQuantumCore
from ..core.visualization.quantum_audit import QuantumAuditVisualizer
import json

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

@ethical_bp.route('/visualize/<state_id>', methods=['GET'])
def visualize_audit(state_id: str):
    """Render interactive audit visualization"""
    try:
        visualizer = QuantumAuditVisualizer()
        
        return jsonify({
            "risk_breakdown": visualizer.create_risk_breakdown_figure(state_id).to_json(),
            "quantum_state": visualizer.create_quantum_state_figure(state_id).to_json()
        })
    except ValueError as e:
        return jsonify({"error": str(e)}), 404

# New Predictive Risk Analysis Endpoint
@ethical_bp.route('/predict/<state_id>', methods=['GET'])
def get_risk_prediction(state_id: str):
    """Get predictive risk analysis"""
    try:
        visualizer = QuantumAuditVisualizer()
        fig = visualizer.create_risk_prediction_figure(state_id)
        return jsonify(fig.to_json())
    except ValueError as e:
        return jsonify({"error": str(e)}), 404

@ethical_bp.route('/visualize/html/<state_id>', methods=['GET'])
def visualize_audit_html(state_id: str):
    """Return complete HTML visualization report"""
    visualizer = QuantumAuditVisualizer()
    
    return f"""
    <html>
        <head>
            <title>Quantum Audit Report - {state_id}</title>
            <script src="https://cdn.plot.ly/plotly-latest.min.js"></script>
        </head>
        <body>
            <div id="risk-breakdown"></div>
            <div id="quantum-state"></div>
            
            <script>
                var riskData = {visualizer.create_risk_breakdown_figure(state_id).to_json()};
                var quantumData = {visualizer.create_quantum_state_figure(state_id).to_json()};
                
                Plotly.newPlot('risk-breakdown', riskData.data, riskData.layout);
                Plotly.newPlot('quantum-state', quantumData.data, quantumData.layout);
            </script>
        </body>
    </html>
    """
