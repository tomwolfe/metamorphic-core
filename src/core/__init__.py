# Add new exports
from .quantum.state_preservation import QuantumStatePreserver
from .ethics.governance import EthicalAuditLogger

__all__ = [
    'QuantumEthicalValidator',
    'EthicalQuantumCore',
    'QuantumStatePreserver',
    'EthicalAuditLogger'
]
