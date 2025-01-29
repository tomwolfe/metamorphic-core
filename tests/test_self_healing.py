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
    def test_healing_loop(self, mock_docker):
        mock_client = MagicMock()
        mock_docker.return_value = mock_client
        mock_client.containers.run.return_value = MagicMock()

        """Test full healing cycle"""
        # Simulate constraint violation
        self.orchestrator.spec.add_safety_invariant("Bias risk never exceeds 0.25")
        self.orchestrator.healing_core.last_healthy_state = None
        
        # Run healing process
        try:
            self.orchestrator.start_healing_loop(interval=1)
            time.sleep(2)
        finally:
            self.orchestrator.stop()
            
        # Verify system state
        self.assertIsNotNone(
            self.orchestrator.healing_core.last_healthy_state,
            "Healing failed to restore system state"
        )

if __name__ == "__main__":
    unittest.main()
