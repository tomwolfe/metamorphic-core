import pytest
import requests
import json

BASE_URL = "http://localhost:5002/genesis"

@pytest.mark.integration
def test_health_endpoint_integration():
    """Test /health endpoint integration for MVP API."""
    response = requests.get(f"{BASE_URL}/health")
    assert response.status_code == 200
    assert response.json() == {"status": "ready"}

@pytest.mark.integration
def test_analyze_ethical_endpoint_code_quality_integration():
    """Integration test for /analyze-ethical endpoint code quality analysis."""
    code_to_analyze = "def test_function():\n  x= 1"  # Code with intentional Flake8 issue (W0612 - Unused variable 'x')
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200
    data = response.json()
    assert "status" in data and data["status"] == "success"
    assert "code_quality" in data
    assert isinstance(data["code_quality"], dict)
    assert "findings" in data["code_quality"]
    assert isinstance(data["code_quality"]["findings"], list)
    assert "output" in data["code_quality"]

    if data["code_quality"]["findings"]: # Check if findings are actually returned
        first_finding = data["code_quality"]["findings"][0]
        assert "file" in first_finding
        assert "line" in first_finding
        assert "col" in first_finding
        assert "code" in first_finding
        assert "msg" in first_finding
        assert "severity" in first_finding
        assert data["code_quality"]["output"] is not None # Verify output is also returned


@pytest.mark.integration
def test_analyze_ethical_endpoint_no_code_integration():
    """Integration test for /analyze-ethical endpoint - no code provided."""
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={},  # No code in payload
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 400
    data = response.json()
    assert "error" in data
    assert data["error"] == "No code provided" # Verify error message for no code