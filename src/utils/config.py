import os
from dotenv import load_dotenv
import re

class ConfigError(Exception):
    pass

class SecureConfig:
    @classmethod
    def load(cls):
        # Load from system environment first
        load_dotenv(override=False)

        missing = [] # Initialize missing list
        invalid = [] # Initialize invalid list

        # Skip validation in CI environments
        is_ci = os.getenv('GITHUB_ACTIONS') == 'true'
        if is_ci:
            return cls

        # Validate required variables
        required = {
            'GEMINI_API_KEY': {
                'min_length': 39,  # "AIzaSy" (7) + 32 chars
                'err_msg': 'Invalid Gemini API key format',
                'pattern': r'^AIzaSy[a-zA-Z0-9_-]{32,35}$'  # Allow 32-35 chars after prefix
            },
            'YOUR_GITHUB_API_KEY': {
                'min_length': 40,
                'err_msg': 'Invalid GitHub API key format',
                'pattern': r'^ghp_[a-zA-Z0-9]{36}$'
            },
            'HUGGING_FACE_API_KEY': {
                'min_length': 34,
                'err_msg': 'Invalid Hugging Face API key format',
                'pattern': r'^hf_[a-zA-Z0-9]{30,}$'  # Allow 30+ chars after prefix
            }
        }
        for var, rules in required.items():
            value = os.getenv(var)
            if not is_ci: # Only validate in non-CI environments
                if not value:
                    missing.append(var)
                elif len(value) < rules['min_length']:
                    invalid.append(f"{var}: {rules['err_msg']}")
                elif 'pattern' in rules and not re.match(rules['pattern'], value):
                    invalid.append(f"{var}: {rules['err_msg']}")


        if missing:
            raise ConfigError(f"Missing required environment variables: {', '.join(missing)}")
        if invalid:
            raise ConfigError(f"Validation errors:\n- " + "\n- ".join(invalid))

        return cls

    @classmethod
    def get(cls, var_name: str, default=None):
        value = os.getenv(var_name, default)
        if value is None and default is None:
            raise ConfigError(f"Environment variable {var_name} not found")
        return value
