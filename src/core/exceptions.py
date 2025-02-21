# src/core/exceptions.py

class AllocationError(Exception):
    """Custom exception for token allocation failures."""
    pass

class FormalVerificationError(Exception):
    """Custom exception for formal verification failures."""
    pass

class InvalidCodeHashError(Exception):
    """Exception for invalid code hash verification."""
    pass

class ModelCapacityError(Exception):
    """Exception for model capacity limits reached."""
    pass

class OrchestrationError(Exception):
    """Base class for orchestration related exceptions."""
    pass

class CriticalFailure(Exception):
    """Exception for critical system failures in orchestration."""
    pass

class MaxSummaryRetriesError(Exception):
    """Exception for exceeding maximum summary retries."""
    pass
