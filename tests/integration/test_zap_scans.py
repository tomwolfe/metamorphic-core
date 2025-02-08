import pytest
from src.core.agents.security_agent import SecurityAgent
import logging
from unittest.mock import patch, MagicMock

# Setup logging
logger = logging.getLogger(__name__)

def test_zap_scan_caching():
    """Test result caching functionality"""
    with patch('src.core.agents.security_agent.ZAPv2') as mock_zap:
        agent = SecurityAgent()
        target_url = "http://flask-app:5000"
        mock_instance = mock_zap.return_value
        mock_instance.ascan.scan.return_value = 'scan-id'
        mock_instance.ascan.status.return_value = 100
        mock_instance.core.alerts.return_value = []
        mock_instance.ascan.set_option_attack_mode.return_value = None  # Mock the missing method
        mock_instance.ascan.set_option_max_depth.return_value = None
        mock_instance.ascan.set_option_max_children.return_value = None
        
        # First scan (should save to cache)
        results = agent.run_zap_baseline_scan(target_url)
        assert results is not None
        cached_results = agent.zap_manager.get_cached_results()
        assert cached_results is not None

        # Second scan should use cached results
        results_second = agent.run_zap_baseline_scan(target_url)
        assert results_second is not None

def test_zap_scan_history():
    """Test scan history tracking"""
    with patch('src.core.agents.security_agent.ZAPv2') as mock_zap:
        agent = SecurityAgent()
        target_url = "http://flask-app:5000"
        mock_instance = mock_zap.return_value
        mock_instance.ascan.scan.return_value = 'scan-id'
        mock_instance.ascan.status.return_value = 100
        mock_instance.core.alerts.return_value = []
        mock_instance.ascan.set_option_attack_mode.return_value = None
        mock_instance.ascan.set_option_max_depth.return_value = None
        mock_instance.ascan.set_option_max_children.return_value = None
        
        # Run multiple scans
        agent.run_zap_baseline_scan(target_url)
        agent.run_zap_baseline_scan(target_url)
        
        history = agent.zap_manager.get_scan_history()
        assert len(history) >= 2
