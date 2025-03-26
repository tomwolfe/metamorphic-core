import pytest
import requests
import os
import json # Import json for loading policy files

# Ensure that the Flask application is running at this URL, adjust if necessary.
# Using 127.0.0.1 explicitly as localhost might resolve differently in some CI environments
BASE_URL = "http://127.0.0.1:5000/genesis" # Correct BASE_URL to include /genesis and specific IP

@pytest.mark.integration
def test_health_endpoint_integration():
    """Test /health endpoint integration for MVP API."""
    response = requests.get(f"{BASE_URL}/health")
    assert response.status_code == 200
    response_json = response.json()
    assert response_json == {"status": "ready"}

# --- Fixtures for Policy Paths ---
@pytest.fixture(scope="module")
def policies_dir():
    # Assumes tests are run from the project root or tests/integration directory
    base = os.path.dirname(__file__)
    # Go up two levels (integration -> tests -> root) then into policies
    policy_path = os.path.abspath(os.path.join(base, '..', '..', 'policies'))
    print(f"DEBUG: Calculated policies_dir: {policy_path}") # Debug print
    if not os.path.isdir(policy_path):
        pytest.fail(f"Policies directory not found at expected location: {policy_path}")
    return policy_path

@pytest.mark.integration
def test_analyze_ethical_default_policy_success_structure(policies_dir):
    """
    Test /analyze-ethical using the DEFAULT policy (strict) with compliant code.
    """
    code_to_analyze = '"""Compliant code."""\ndef test_function():\n  """Docstring"""\n  print("hello")'
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
    assert response_json["status"] == "approved" # Check approved status specifically
    assert "requested_policy_name" in response_json # Check new field
    assert "code_quality" in response_json # As per Week 2 completion (Placeholder in Week 4 API code)
    assert "ethical_analysis" in response_json # As per Week 3/4 task
    assert "generated_tests_placeholder" in response_json # As per Week 4 plan (Placeholder in Week 4 API code)

    # Verify the default policy was used
    default_policy_path = os.path.join(policies_dir, 'policy_bias_risk_strict.json')
    with open(default_policy_path, 'r') as f: default_policy_name = json.load(f)['policy_name']
    assert response_json["requested_policy_name"] == default_policy_name

    # Verify the 'ethical_analysis' section structure
    assert isinstance(response_json["ethical_analysis"], dict)
    analysis_section = response_json["ethical_analysis"]

    assert "policy_name" in analysis_section
    assert "description" in analysis_section
    assert "overall_status" in analysis_section # Check for overall_status from engine
    assert analysis_section["overall_status"] == "approved" # Check engine status too
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
        assert analysis_section[constraint_key]["status"] == "compliant"

# --- Tests for Dynamic Policy Loading (Week 5) ---

@pytest.mark.integration
def test_analyze_ethical_request_moderate_policy_success(policies_dir):
    """Test requesting the 'moderate' policy and verifying its application."""
    policy_name_req = "policy_safety_moderate"
    # Code that violates strict safety (os.system) but might pass moderate (depends on exact rules)
    # Let's use code that is compliant with moderate but maybe not strict bias
    code_to_analyze = '"""Docstring present."""\ndef safe_ish():\n  # Contains "offensive language" which might fail strict but pass moderate\n  print("offensive language")'

    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200
    response_json = response.json()

    # Verify the moderate policy was used
    moderate_policy_path = os.path.join(policies_dir, f'{policy_name_req}.json')
    with open(moderate_policy_path, 'r') as f: moderate_policy_name_actual = json.load(f)['policy_name']
    assert response_json["requested_policy_name"] == moderate_policy_name_actual

    # Check status based on moderate policy rules (example: bias might pass, safety passes)
    assert response_json["status"] == "approved" # Assuming moderate allows "offensive language"
    assert response_json["ethical_analysis"]["BiasRisk"]["status"] == "compliant" # Moderate threshold might be higher
    assert response_json["ethical_analysis"]["TransparencyScore"]["status"] == "compliant"
    assert response_json["ethical_analysis"]["SafetyBoundary"]["status"] == "compliant"

@pytest.mark.integration
def test_analyze_ethical_request_minimum_policy_violation(policies_dir):
    """Test requesting the 'minimum' policy with code violating its transparency."""
    policy_name_req = "policy_transparency_minimum"
    code_to_analyze = "def no_docstring():\n    pass" # Violates transparency

    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200 # Request is valid, analysis performed
    response_json = response.json()

    # Verify the minimum policy was used
    minimum_policy_path = os.path.join(policies_dir, f'{policy_name_req}.json')
    with open(minimum_policy_path, 'r') as f: minimum_policy_name_actual = json.load(f)['policy_name']
    assert response_json["requested_policy_name"] == minimum_policy_name_actual

    # Check status based on minimum policy rules (transparency fails)
    assert response_json["status"] == "rejected"
    assert response_json["ethical_analysis"]["TransparencyScore"]["status"] == "violation"
    assert response_json["ethical_analysis"]["BiasRisk"]["status"] == "compliant"
    assert response_json["ethical_analysis"]["SafetyBoundary"]["status"] == "compliant"

@pytest.mark.integration
def test_analyze_ethical_request_nonexistent_policy():
    """Test requesting a policy file that does not exist."""
    policy_name_req = "nonexistent_policy_123"
    code_to_analyze = "print('hello')"

    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 404 # Expect Not Found
    response_json = response.json()
    assert response_json["status"] == "error"
    assert f"Policy '{policy_name_req}' not found" in response_json["message"]

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
    assert "status" in response_json
    assert response_json["status"] == "error"
    assert "message" in response_json

@pytest.mark.integration
def test_analyze_ethical_request_invalid_policy_name_format():
    """Test requesting a policy with invalid characters in the name."""
    policy_name_req = "../etc/passwd" # Invalid format
    code_to_analyze = "print('hello')"

    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 400 # Expect Bad Request
    response_json = response.json()
    assert response_json["status"] == "error"
    assert f"Invalid policy name format: {policy_name_req}" in response_json["message"]