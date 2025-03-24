import pytest
import requests
import os

# Ensure that the Flask application is running at this URL, adjust if necessary.
BASE_URL = "http://localhost:5002/genesis"  # Correct BASE_URL to include /genesis and port 5002

@pytest.mark.integration
def test_health_endpoint_integration():
    """Test /health endpoint integration for MVP API."""
    response = requests.get(f"{BASE_URL}/health")
    assert response.status_code == 200

@pytest.mark.integration
def test_analyze_ethical_endpoint_code_quality_integration():
    """Integration test for /analyze-ethical endpoint code quality analysis."""
    code_to_analyze = "def test_function():\n  x= 1"  # Sample code
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200

@pytest.mark.integration
def test_analyze_ethical_endpoint_no_code_integration():
    """Integration test for /analyze-ethical endpoint - no code provided."""
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={},  # No code in payload
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 400 # Expecting 400 for bad request due to missing code