# Add new exports
from .quantum.state_preservation import QuantumStatePreserver
from .ethics.governance import EthicalAuditLogger
from .ethics.governance import QuantumEthicalValidator
from .quantum.ethical_validation import EthicalQuantumCore
import os
import sys

# Ensure core modules are importable
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

__all__ = [
    'QuantumEthicalValidator',
    'EthicalQuantumCore',
    'QuantumStatePreserver',
    'EthicalAuditLogger'
]
