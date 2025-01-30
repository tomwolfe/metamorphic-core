# tests/test_self_healing.py
from unittest.mock import patch
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import unittest
from src.core.self_healing.orchestrator import HealingOrchestrator
from unittest.mock import patch, MagicMock

class TestSelfHealing(unittest.TestCase):
    @patch('src.core.ethics.governance.EthicalGovernanceEngine')
    @patch('docker.from_env')
    @patch('subprocess.run')
    @patch('src.core.self_healing.orchestrator.HealingOrchestrator._needs_intervention', return_value=True)
    @patch('time.sleep', return_value=None)
    def test_healing_loop(mock_sleep, mock_needs, mock_run, mock_docker, mock_ethics):
        mock_ethics.return_value.get_ethical_model_version.return_value = "v2.3.1"
        mock_client = MagicMock()
        mock_docker.return_value = mock_client
        
        orchestrator = HealingOrchestrator()
        orchestrator.start_healing_loop(interval=1)
        orchestrator.stop()
        
        assert mock_client.containers.run.called
        
if __name__ == "__main__":
    unittest.main()
