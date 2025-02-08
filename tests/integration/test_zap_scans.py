import pytest
from src.core.agents.security_agent import SecurityAgent
import logging
from unittest.mock import patch, MagicMock
from src.utils.config import SecureConfig

# Setup logging
logger = logging.getLogger(__name__)

@pytest.fixture
def test_security_agent():
    """Fixture to provide a SecurityAgent with mocked dependencies."""
    with patch('src.utils.config.SecureConfig.get') as mock_config, \
         patch('src.core.agents.security_agent.ZAPv2') as mock_zap:
        
        # Setup mock environment variables
        mock_config.side_effect = {
            'GEMINI_API_KEY': 'test-key',
            'YOUR_GITHUB_API_KEY': 'github-test-key',
            'HUGGING_FACE_API_KEY': 'huggingface-test-key',
            'ZAP_API_KEY': 'zap-test-key'
        }.get
        
        # Setup ZAP mock
        mock_zap_instance = mock_zap.return_value
        mock_zap_instance.ascan.scan.return_value = 'scan-id'
        mock_zap_instance.ascan.status.return_value = 100
        mock_zap_instance.core.alerts.return_value = []
        mock_zap_instance.ascan.set_option_attack_mode.return_value = None
        mock_zap_instance.ascan.set_option_max_depth.return_value = None
        mock_zap_instance.ascan.set_option_max_children.return_value = None

        # Initialize SecurityAgent with mocked dependencies
        agent = SecurityAgent()
        
        yield {
            'agent': agent,
            'zap': mock_zap_instance
        }

def test_zap_scan_caching(test_security_agent):
    """Test result caching functionality"""
    agent = test_security_agent['agent']
    target_url = "http://flask-app:5000"
    
    # First scan (should save to cache)
    results = agent.run_zap_baseline_scan(target_url)
    assert results is not None
    cached_results = agent.zap_manager.get_cached_results()
    assert cached_results is not None

    # Second scan should use cached results
    results_second = agent.run_zap_baseline_scan(target_url)
    assert results_second is not None

def test_zap_scan_history(test_security_agent):
    """Test scan history tracking"""
    agent = test_security_agent['agent']
    target_url = "http://flask-app:5000"
    
    # Run multiple scans
    agent.run_zap_baseline_scan(target_url)
    agent.run_zap_baseline_scan(target_url)
    
    history = agent.zap_manager.get_scan_history()
    assert len(history) >= 2
