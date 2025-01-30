# tests/test_self_healing.py
from unittest.mock import patch
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import unittest
from src.core.self_healing.orchestrator import HealingOrchestrator
from unittest.mock import patch, MagicMock

class TestSelfHealing(unittest.TestCase):
    @patch('subprocess.run')  # Fix patch target
    @patch('docker.from_env')
    def test_healing_loop(self, mock_docker, mock_run):
        # Mock Docker client
        mock_client = MagicMock()
        mock_docker.return_value = mock_client
        
        # Mock container creation
        mock_container = MagicMock()
        mock_container.logs.return_value = b"No errors"
        mock_client.containers.run.return_value = mock_container
        
        # Initialize orchestrator with mocked dependencies
        orchestrator = HealingOrchestrator()
        orchestrator.start_healing_loop(interval=1)
        time.sleep(1)
        orchestrator.stop()
        
        # Verify container run was attempted
        mock_client.containers.run.assert_called_once()
        
if __name__ == "__main__":
    unittest.main()
