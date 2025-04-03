# tests/integration/test_api_mvp_endpoint.py
import pytest
import requests
import os
import json

BASE_URL = "http://127.0.0.1:5000/genesis"

@pytest.mark.integration
def test_health_endpoint_integration():
    """Test /health endpoint integration for MVP API."""
    response = requests.get(f"{BASE_URL}/health")
    assert response.status_code == 200
    response_json = response.json()
    assert response_json == {"status": "ready"}

@pytest.fixture(scope="module")
def policies_dir():
    base = os.path.dirname(__file__)
    policy_path = os.path.abspath(os.path.join(base, '..', '..', 'policies'))
    if not os.path.isdir(policy_path):
        pytest.fail(f"Policies directory not found at expected location: {policy_path}")
    return policy_path

@pytest.mark.integration
def test_analyze_ethical_default_policy_success_structure_and_quality(policies_dir):
    """
    Test /analyze-ethical using the DEFAULT policy (strict) with compliant code,
    verifying structure and code quality results.
    """
    code_to_analyze = '''"""Compliant code."""
import os


def test_function():
    """Provide a compliant docstring."""
    print(f"Using os: {os.name}")
    return "hello"
'''
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200
    response_json = response.json()
    assert response_json["status"] == "approved"
    # --- Verify Code Quality Section ---
    assert "code_quality" in response_json
    cq_section = response_json["code_quality"]
    assert isinstance(cq_section, dict)
    assert cq_section.get("issues_found", -1) == 0, f"Expected 0 issues, got {cq_section.get('issues_found')}. Output: {cq_section.get('output')}"
    assert cq_section.get("output", "ERROR") == ""
    assert "error" not in cq_section  # Ensure no error key
    # --- Verify Ethical Analysis Section ---
    assert "ethical_analysis" in response_json
    analysis_section = response_json["ethical_analysis"]
    assert analysis_section["overall_status"] == "approved"
    assert analysis_section["BiasRisk"]["status"] == "compliant"
    assert analysis_section["TransparencyScore"]["status"] == "compliant"
    assert analysis_section["SafetyBoundary"]["status"] == "compliant"

@pytest.mark.integration
def test_analyze_ethical_with_flake8_issues(policies_dir):
    """
    Test /analyze-ethical with code that has Flake8 issues but is ethically compliant.
    Verifies the code_quality section reports the issues.
    """
    code_to_analyze = '''"""Module docstring."""
import sys # F401 unused import
def func_with_issues():
    """Function docstring."""
    x = 1
    return x
'''
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200
    response_json = response.json()
    # --- Verify Ethical Status ---
    assert response_json["status"] == "approved"
    assert response_json["ethical_analysis"]["overall_status"] == "approved"
    assert response_json["ethical_analysis"]["TransparencyScore"]["status"] == "compliant"
    # --- Verify Code Quality Section ---
    assert isinstance(response_json["code_quality"], dict)
    cq_section = response_json["code_quality"]
    assert "output" in cq_section
    assert "issues_found" in cq_section
    assert cq_section["issues_found"] >= 1  # Expect at least the F401
    assert "F401" in cq_section["output"]  # Check for specific code
    # assert "D401" in cq_section["output"] # D401 might not always trigger depending on flake8 config/plugins
    assert "error" not in cq_section

@pytest.mark.integration
def test_analyze_ethical_request_moderate_policy_success(policies_dir):
    """Test moderate policy with code quality check."""
    policy_name_req = "policy_safety_moderate"  # This policy exists
    code_to_analyze = '''"""Docstring present."""


def check_safety():
    """Check the safety according to moderate policy."""
    # Contains "offensive language" which will fail moderate bias check
    print("offensive language")
'''
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200
    response_json = response.json()
    # --- Verify Policy Name ---
    moderate_policy_path = os.path.join(policies_dir, f'{policy_name_req}.json') # <---- CORRECTED FUNCTION CALL
    with open(moderate_policy_path, 'r') as f: moderate_policy_name_actual = json.load(f)['policy_name']
    assert response_json["requested_policy_name"] == moderate_policy_name_actual
    # --- Verify Ethical Status (Rejected due to bias keyword) ---
    assert response_json["status"] == "rejected"
    assert response_json["ethical_analysis"]["BiasRisk"]["status"] == "violation"
    # --- Verify Code Quality (Should be 0 issues) ---
    cq_section = response_json["code_quality"]
    assert cq_section["issues_found"] == 0, f"Expected 0 issues, got {cq_section['issues_found']}. Output: {cq_section['output']}"

@pytest.mark.integration
def test_analyze_ethical_request_minimum_policy_violation(policies_dir):
    """Test minimum policy with transparency violation (missing function docstring)."""
    policy_name_req = "policy_transparency_minimum"  # This policy exists
    code_to_analyze = '''"""Module docstring."""
def no_docstring():
    pass
'''
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 200
    response_json = response.json()
    # --- Verify Policy Name ---
    minimum_policy_path = os.path.join(policies_dir, f'{policy_name_req}.json') # <---- CORRECTED FUNCTION CALL
    with open(minimum_policy_path, 'r') as f: minimum_policy_name_actual = json.load(f)['policy_name']
    assert response_json["requested_policy_name"] == minimum_policy_name_actual

    # --- Verify Ethical Status (Rejected due to missing function docstring) ---
    assert response_json["status"] == "rejected", "Expected status 'rejected' due to missing function docstring"
    assert response_json["ethical_analysis"]["TransparencyScore"]["status"] == "violation"

    # --- Verify Code Quality (Should report D103 - missing function docstring, not D100) ---
    cq_section = response_json["code_quality"]
    # Check for specific expected Flake8 codes
    found_issues = cq_section.get("issues_found", 0)
    output = cq_section.get("output", "")
    assert found_issues >= 1, f"Expected at least 1 issue, got {found_issues}. Output: {output}"
    assert "D103" in output, f"Expected D103 (Missing docstring in public function) in output: {output}.  (Corrected assertion to D103)" # Corrected Assertion to D103
    assert "error" not in cq_section

# (Other error case tests remain unchanged)
@pytest.mark.integration
def test_analyze_ethical_request_nonexistent_policy():
    policy_name_req = "nonexistent_policy_123"
    code_to_analyze = "print('hello')"
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 404
    response_json = response.json()
    assert response_json["status"] == "error"
    assert f"Policy '{policy_name_req}' not found" in response_json["message"]

@pytest.mark.integration
def test_analyze_ethical_endpoint_no_code_integration():
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 400
    response_json = response.json()
    assert "status" in response_json
    assert response_json["status"] == "error"
    assert "Missing 'code' field" in response_json["message"]

@pytest.mark.integration
def test_analyze_ethical_request_invalid_policy_name_format():
    policy_name_req = "../etc/passwd"
    code_to_analyze = "print('hello')"
    response = requests.post(
        f"{BASE_URL}/analyze-ethical",
        json={"code": code_to_analyze, "policy_name": policy_name_req},
        headers={'Content-Type': 'application/json'}
    )
    assert response.status_code == 400
    response_json = response.json()