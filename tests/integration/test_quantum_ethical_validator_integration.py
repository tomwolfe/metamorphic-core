import unittest
from unittest import TestCase
from src.core.ethics.governance import QuantumEthicalValidator

class TestQuantumEthicalValidator(TestCase):
    def setUp(self) -> None:
        self.validator = QuantumEthicalValidator()

    def test_init(self):
        """Test if QuantumEthicalValidator initializes correctly with required components"""
        self.assertTrue(hasattr(self.validator, 'spec_analyzer'), 
                       "spec_analyzer attribute not found")
        self.assertTrue(hasattr(self.validator.spec_analyzer, 'knowledge_graph'),
                       "knowledge_graph not initialized in spec_analyzer")

    def test_validate_code(self):
        """Test if code validation includes specification analysis"""
        sample_code = "print('Hello, World!')"
        result = self.validator.validate_code(sample_code)
        self.assertIn('spec_analysis', result, "spec_analysis missing in validation result")
        self.assertIsInstance(result['spec_analysis'], dict, 
                             "spec_analysis should be a dictionary")

if __name__ == "__main__":
    unittest.main()
