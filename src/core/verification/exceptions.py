class FormalVerificationError(Exception):
    """Custom exception for formal verification failures."""
    pass

class InvalidCodeHashError(Exception):
    """Exception for invalid code hash verification."""
    pass

class ModelCapacityError(Exception): # Assuming OrchestrationError exists or define it
    """Exception for model capacity limits reached."""
    pass

class OrchestrationError(Exception): # Define OrchestrationError if not already defined
    """Base class for orchestration related exceptions."""
    pass

class CriticalFailure(Exception): # Define CriticalFailure if not already defined
    """Exception for critical system failures in orchestration."""
    pass

class MaxSummaryRetriesError(Exception):
    """Exception for exceeding maximum summary retries."""
    pass
