# tests/integration/test_zap_scans.py
import pytest
import subprocess
import time
import os
from src.core.agents.security_agent import SecurityAgent
from src.core.knowledge_graph import KnowledgeGraph

@pytest.fixture(scope="module")
def docker_compose_project():
    """Fixture to start and stop the docker-compose project for integration tests."""
    subprocess.run(["docker", "compose", "-f", "docker-compose.yml", "up", "-d"], check=True)
    time.sleep(10)  # Give services time to start - adjust as needed
    yield
    subprocess.run(["docker", "compose", "-f", "docker-compose.yml", "down"], check=True)

@pytest.mark.integration
def test_zap_scan_integration_live(docker_compose_project):
    """
    Test ZAP baseline scan integration with a live Flask app and ZAP instance.
    Requires Docker Compose to be running.
    """
    agent = SecurityAgent()
    target_url = "http://localhost:5000/health" # Use health endpoint for quick test

    # Ensure Flask app is ready (health endpoint should return 200)
    max_attempts = 10
    attempt = 0
    app_ready = False
    while attempt < max_attempts:
        try:
            result = subprocess.run(["curl", "-f", target_url], capture_output=True, check=True)
            if result.returncode == 0:
                app_ready = True
                break
        except subprocess.CalledProcessError:
            time.sleep(2)
            attempt += 1
    assert app_ready, "Flask app health endpoint not reachable after multiple attempts."


    scan_results = agent.run_zap_baseline_scan(target_url)
    assert isinstance(scan_results, dict), "ZAP scan should return a dictionary"
    assert "alerts" in scan_results, "Scan results should contain alerts"

    kg = KnowledgeGraph()
    # Basic check for vulnerabilities in KG (may vary depending on app)
    vulnerability_nodes = kg.search("ZAP Finding")
    assert vulnerability_nodes is not None, "No vulnerability findings found in KG"
    if vulnerability_nodes: # Only check if nodes are found
        assert any("ZAP Finding" in node.content for node in vulnerability_nodes), "KG nodes do not contain 'ZAP Finding'"
        assert any(target_url in node.metadata.get('target_url', '') for node in vulnerability_nodes), "KG nodes do not have correct target URL in metadata"
