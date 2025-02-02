from flask import Blueprint, request, jsonify, current_app
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address

from src.core.ethics.governance import QuantumEthicalValidator
from src.core.quantum.ethical_validation import EthicalQuantumCore
from src.core.visualization.quantum_audit import QuantumAuditVisualizer
from src.core.llm_orchestration import format_math_prompt, extract_boxed_answer
from src.core.agents.security_agent import SecurityAgent # Import SecurityAgent
import json

ethical_bp = Blueprint('ethical', __name__)
validator = QuantumEthicalValidator()
quantum_core = EthicalQuantumCore()
visualizer = QuantumAuditVisualizer() # Instantiate QuantumAuditVisualizer once
security_agent = SecurityAgent() # Instantiate SecurityAgent

limiter = Limiter(
    get_remote_address,
    app=current_app,
    default_limits=["200 per day, 50 per hour"],
    storage_uri="memory://" # or redis://localhost:6379
)

# Add new endpoint
@ethical_bp.route('/solve-math', methods=['POST'])
@limiter.limit("3/minute")
def solve_math_problem():
    problem = request.json.get('problem')
    problem = security_agent.sanitize_input(problem) # Sanitize input
    if not problem:
        return jsonify({"error": "No problem provided or invalid input"}), 400

    try:
        formatted_prompt = format_math_prompt(problem)
        response = current_app.llm_orchestrator.generate(formatted_prompt)
        return jsonify({
            "solution": extract_boxed_answer(response),
            "full_response": response
        })
    except RuntimeError as e:
        return jsonify({"error": str(e)}), 500

@ethical_bp.route('/analyze', methods=['POST'])
def ethical_analysis():
    code = request.json.get('code')
    code = security_agent.sanitize_input(code) # Sanitize code input
    if not code:
        return jsonify({"error": "No code provided or invalid input"}), 400

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
        fig = visualizer.create_risk_prediction_figure(state_id)
        return jsonify(fig.to_json())
    except ValueError as e:
        return jsonify({"error": str(e)}), 404

@ethical_bp.route('/visualize/html/<state_id>', methods=['GET'])
def visualize_audit_html(state_id: str):
    """Return complete HTML visualization report"""
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
