# tests/integration/test_zap_scans.py
from src.core.agents.security_agent import SecurityAgent
from src.core.knowledge_graph import KnowledgeGraph
import pytest
import logging

def test_zap_scan_manager_init():
    """Test ZAP Scan Manager initialization"""
    agent = SecurityAgent()
    assert agent.zap_manager is not None
    assert len(agent.zap_manager.config_presets) == 3
    assert "strict" in agent.zap_manager.config_presets

def test_zap_scan_with_config_presets():
    """Test scan with different configuration presets"""
    agent = SecurityAgent()
    target_url = "http://flask-app:5000"
    
    # Test with strict config
    results = agent.run_zap_baseline_scan(target_url, "strict")
    assert "alerts" in results
    
    # Test with standard config
    results = agent.run_zap_baseline_scan(target_url, "standard")
    assert "alerts" in results

def test_zap_scan_caching():
    """Test result caching functionality"""
    agent = SecurityAgent()
    target_url = "http://flask-app:5000"
    
    # First scan (should save to cache)
    results = agent.run_zap_baseline_scan(target_url)
    assert agent.zap_manager.get_cached_results() is not None
    
    # Second scan (should use cache)
    results = agent.run_zap_baseline_scan(target_url)
    assert "Using cached scan results" in [record.getMessage() for record in logging.root.handlers[0].buffer]

def test_zap_scan_history():
    """Test scan history tracking"""
    agent = SecurityAgent()
    target_url = "http://flask-app:5000"
    
    # Run multiple scans and check history
    agent.run_zap_baseline_scan(target_url)
    agent.run_zap_baseline_scan(target_url)
    
    history = agent.zap_manager.get_scan_history()
    assert len(history) >= 2
    assert "high_risk" in history[0]
    assert "medium_risk" in history[0]
