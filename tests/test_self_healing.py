# tests/test_self_healing.py
from unittest.mock import patch
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import unittest
from src.core.self_healing.orchestrator import HealingOrchestrator
from unittest.mock import patch, MagicMock

class TestSelfHealing(unittest.TestCase):
    @patch('src.core.self_healing.orchestrator.HealingOrchestrator._needs_intervention', return_value=True)
    @patch('src.core.self_healing.core.docker.from_env')
    @patch('src.core.ethics.governance.EthicalGovernanceEngine')
    @patch('time.sleep', side_effect=KeyboardInterrupt)  # Force loop exit
    def test_healing_loop(self, mock_sleep, mock_ethics, mock_docker, mock_needs):
        mock_client = MagicMock()
        mock_docker.return_value = mock_client
        
        orchestrator = HealingOrchestrator()
        orchestrator.start_healing_loop(interval=1)
        
        # Verify at least one monitoring cycle occurred
        self.assertTrue(mock_needs.called)
        
if __name__ == "__main__":
    unittest.main()
