# tests/test_self_healing.py
from unittest.mock import patch
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import unittest
from src.core.self_healing.orchestrator import HealingOrchestrator

class TestSelfHealing(unittest.TestCase):
    def setUp(self):
        self.orchestrator = HealingOrchestrator()

    @patch('docker.from_env')
    @patch('src.core.self_healing.core.subprocess.run')
    def test_healing_loop(self, mock_run, mock_docker):
        mock_client = MagicMock()
        mock_docker.return_value = mock_client
        mock_container = MagicMock()
        mock_client.containers.run.return_value = mock_container
        mock_container.logs.return_value = b"No errors"
        
        self.orchestrator.spec.add_safety_invariant("Bias risk never exceeds 0.25")
        self.orchestrator.start_healing_loop(interval=1)
        time.sleep(1)
        self.orchestrator.stop()
        
        self.assertTrue(mock_client.containers.run.called)
        
if __name__ == "__main__":
    unittest.main()
