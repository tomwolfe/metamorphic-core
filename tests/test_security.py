# tests/test_security.py
import pytest
import os
from unittest.mock import patch, MagicMock
from src.core.agents.security_agent import SecurityAgent
from src.utils.config import SecureConfig
import logging
import subprocess

def test_zap_scan_integration():
    """Test ZAP baseline scan integration - requires Docker in CI"""
    logger = logging.getLogger(__name__)
    with patch('src.utils.config.SecureConfig.get') as mock_get:
        mock_get.side_effect = lambda var_name, default=None: {
            'GEMINI_API_KEY': 'test_key',
            'YOUR_GITHUB_API_KEY': 'test_key',
            'HUGGING_FACE_API_KEY': 'test_key',
            'ZAP_API_KEY': 'test_zap_key'  # Added ZAP_API_KEY
        }.get(var_name, default)
        agent = SecurityAgent()
        target_url = "http://localhost:5000/generate"

        try:
            subprocess.check_output(["docker", "compose", "ps"], text=True)
        except subprocess.CalledProcessError as e:
            pytest.fail(f"Docker Compose services not running. Error: {e}")

        results = agent.run_zap_baseline_scan(target_url)
        assert isinstance(results, dict), "ZAP scan should return a dictionary"
        assert "alerts" in results, "Scan results should contain alerts"
