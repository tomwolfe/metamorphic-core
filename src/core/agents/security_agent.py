from src.utils.config import SecureConfig
from typing import Optional
import re
import logging
import json

class SecurityAgent:
    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self._validate_environment()

    def _validate_environment(self) -> bool:
        """Validate all security-critical environment variables"""
        try:
            SecureConfig.load()
            required_vars = ['GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY', 'HUGGING_FACE_API_KEY']
            for var in required_vars:
                value = SecureConfig.get(var)
                if not value or value == 'invalid' or value.startswith('your_'):
                    raise ValueError(f"Invalid configuration for {var}")
            return True
        except Exception as e:
            self.logger.critical(f"Environment validation failed: {str(e)}")
            raise

    def sanitize_input(self, input_str: str, max_length: int = 1000) -> Optional[str]:
        """Basic input sanitization for API endpoints"""
        if not input_str:
            return None

        # Remove '@' and other specified non-allowed characters
        sanitized = re.sub(r'[^a-zA-Z0-9\s_\-\.,:;!?]', '', input_str)[:max_length]
        return sanitized.strip()
