# tests/test_self_healing.py
from unittest.mock import patch
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import unittest
from src.core.self_healing.orchestrator import HealingOrchestrator
from unittest.mock import patch, MagicMock

class TestSelfHealing(unittest.TestCase):
    @patch('time.sleep')  # Mock sleep to prevent hanging
    @patch('src.core.self_healing.orchestrator.HealingOrchestrator._needs_intervention', return_value=True)
    def test_healing_loop(self, mock_needs, mock_sleep, mock_run, mock_docker, mock_ethics):
        mock_ethics.return_value.get_ethical_model_version.return_value = "v2.3.1"
        mock_client = MagicMock()
        mock_docker.return_value = mock_client
        
        mock_container = MagicMock()
        mock_container.logs.return_value = b"No errors"
        mock_client.containers.run.return_value = mock_container
        
        orchestrator = HealingOrchestrator()
        orchestrator.start_healing_loop(interval=1)
        orchestrator.stop()  # Immediate stop after starting
        
        mock_client.containers.run.assert_called_once()
        
if __name__ == "__main__":
    unittest.main()
