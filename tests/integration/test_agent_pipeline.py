# tests/integration/test_agent_pipeline.py
import pytest
from src.core.ethics.governance import QuantumEthicalValidator

@pytest.fixture(scope="module")
def validator():
    """Fixture to provide a QuantumEthicalValidator with mocked environment variables."""
    with patch('src.utils.config.SecureConfig') as mock_secure_config:
        # Mock the get method to return predefined values
        mock_secure_config.get.side_effect = lambda var_name, default=None: {
            'GEMINI_API_KEY': 'test_gemini_key',
            'YOUR_GITHUB_API_KEY': 'test_github_key',
            'HUGGING_FACE_API_KEY': 'test_hf_key',
            'ZAP_API_KEY': 'test_zap_key',
            # Add any other required environment variables here
            # For example:
            'LLM_PROVIDER': 'gemini',
            'LLM_MAX_RETRIES': '3',
            'LLM_TIMEOUT': '30'
        }.get(var_name, default)
        
        # Mock the load method to prevent actual environment checks
        mock_secure_config.load.return_value = None
        
        return QuantumEthicalValidator()
