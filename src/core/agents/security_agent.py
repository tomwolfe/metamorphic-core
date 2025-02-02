from src.utils.config import SecureConfig, ConfigError # Import ConfigError
from typing import Optional
import re
import logging
import json
import os # Import os for potential config error fix

class SecurityAgent:
    def __init__(self):
        self.logger = logging.getLogger(__name__)
        try:
            self._validate_environment()
        except ValueError as e:
            raise e # Re-raise ValueError to be caught by tests expecting ValueError
        except ConfigError as e:
            raise e # Re-raise ConfigError to be caught by tests expecting ConfigError


    def _validate_environment(self) -> bool:
        """Validate all security-critical environment variables"""
        try:
            SecureConfig.load()
            required_vars = ['GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY', 'HUGGING_FACE_API_KEY']
            for var in required_vars:
                if var not in os.environ: # Check if the env var exists at all first, before SecureConfig.get which might return None and mask missing var error
                    raise ConfigError(f"Missing required environment variable: {var}") # Raise ConfigError for missing env vars
                value = SecureConfig.get(var)
                if not value or value == 'invalid' or value.startswith('your_'):
                    raise ValueError(f"Invalid configuration for {var}") # Keep ValueError for invalid values, but after checking for missing vars
            return True
        except (ValueError, ConfigError) as e: # Catch both Value and ConfigError
            self.logger.critical(f"Environment validation failed: {str(e)}")
            raise e # Re-raise the caught exception


    def sanitize_input(self, input_str: str, max_length: int = 1000) -> Optional[str]:
        """Basic input sanitization for API endpoints"""
        if not input_str:
            return None

        # Remove '@' and other specified non-allowed characters
        sanitized = re.sub(r'[^a-zA-Z0-9\s_\-\.,:;!?]', '', input_str)[:max_length]
        return sanitized.strip()

    def audit_security_event(self, event_type: str, details: dict):
        """Log security events with structured formatting"""
        self.logger.info(f"SECURITY_EVENT|{event_type}|{json.dumps(details)}")
