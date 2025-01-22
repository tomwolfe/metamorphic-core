import plotly.io as pio
from src.core.visualization.quantum_audit import QuantumAuditVisualizer

def test_visualization(state_id: str):
    """Generate and display sample visualization"""
    visualizer = QuantumAuditVisualizer()
    
    # Generate figures
    risk_fig = visualizer.create_risk_breakdown_figure(state_id)
    quantum_fig = visualizer.create_quantum_state_figure(state_id)
    
    # Save as HTML
    pio.write_html(risk_fig, "risk_breakdown.html")
    pio.write_html(quantum_fig, "quantum_state.html")
    
    print("Visualizations saved as HTML files:")
    print("- risk_breakdown.html")
    print("- quantum_state.html")

if __name__ == "__main__":
    test_visualization("QSTATE_20250121221017935992")  # Use your state ID
