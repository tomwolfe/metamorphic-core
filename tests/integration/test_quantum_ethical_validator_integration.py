# File: tests/integration/test_quantum_ethical_validator_integration.py
import unittest
from src.core.ethics.governance import QuantumEthicalValidator
from src.core.knowledge_graph import KnowledgeGraph

class TestQuantumEthicalValidator(unittest.TestCase):
    def setUp(self):
        self.validator = QuantumEthicalValidator()
        
    def test_spec_analysis_integration(self):
        valid_code = "def example():\n    print('Hello World')"
        result = self.validator.validate_code(valid_code)
        
        self.assertIn('spec_analysis', result)
        self.assertGreater(len(result['spec_analysis']['functions']), 0)
        
        # Verify KG storage
        kg = KnowledgeGraph()
        results = kg.search("spec_analysis")
        self.assertTrue(any(n.type == "spec_analysis" for n in results))
