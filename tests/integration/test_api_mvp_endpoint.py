import pytest
import requests
import os

# Ensure that the Flask application is running at this URL, adjust if necessary.
BASE_URL = "http://localhost:5000/genesis"  # Correct BASE_URL to include /genesis and port 5000

@pytest.mark.integration
def test_health_endpoint_integration():
    """Test /health endpoint integration for MVP API."""
    response = requests.get(f"{BASE_URL}/health")
    assert response.status_code == 200
    response_json = response.json()
    assert response_json == {"status": "ready"}

@pytest.mark.integration
def test_analyze_ethical_endpoint_success_structure(): # Renamed test for clarity
    """
    Integration test for /analyze-ethical endpoint success response structure,
    including ethical_analysis verification.
    """
    # Using compliant code according to the default strict policy for simplicity
    code_to_analyze = '"""Compliant code."""\ndef test_function():\n  print("hello")'
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200

    # --- Added Assertions for Response Structure ---
    response_json = response.json()

    # Check top-level keys expected in MVP success response
    assert "status" in response_json
    assert response_json["status"] == "success" # Check success status specifically
    assert "code_quality" in response_json # As per Week 2 completion
    assert "ethical_analysis" in response_json # As per Week 3 task
    assert "generated_tests_placeholder" in response_json # As per Week 4 plan

    # Verify the 'ethical_analysis' section structure
    assert isinstance(response_json["ethical_analysis"], dict)
    analysis_section = response_json["ethical_analysis"]

    assert "policy_name" in analysis_section
    assert "description" in analysis_section
    assert "BiasRisk" in analysis_section
    assert "TransparencyScore" in analysis_section
    assert "SafetyBoundary" in analysis_section

    # Check structure within each constraint key
    for constraint_key in ["BiasRisk", "TransparencyScore", "SafetyBoundary"]:
        assert isinstance(analysis_section[constraint_key], dict)
        assert "status" in analysis_section[constraint_key]
        assert "threshold" in analysis_section[constraint_key]
        assert "enforcement_level" in analysis_section[constraint_key]
        # Optionally check status value for this specific compliant code + default policy
        # assert analysis_section[constraint_key]["status"] == "compliant"

@pytest.mark.integration
def test_analyze_ethical_endpoint_no_code_integration():
    """Integration test for /analyze-ethical endpoint - no code provided."""
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={},  # No code in payload
        headers={'Content-Type': 'application/json'}
    )
    # Verify 400 Bad Request status and error message
    assert response.status_code == 400
    response_json = response.json()
    assert "error" in response_json
    assert response_json["error"] == "No code provided"