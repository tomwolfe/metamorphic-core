import os
import logging
from dotenv import load_dotenv
import re

class ConfigError(Exception):
    pass

class SecureConfig:
    @classmethod
    def load(cls):
        load_dotenv(override=False)
        missing = []
        invalid = []
        is_ci = os.getenv('GITHUB_ACTIONS') == 'true'

        required = {
            'GEMINI_API_KEY': {
                'min_length': 39,
                'err_msg': 'Invalid Gemini API key format',
                'pattern': r'^AIzaSy[a-zA-Z0-9_-]{32,35}$'
            },
            'YOUR_GITHUB_API_KEY': {
                'min_length': 40,
                'err_msg': 'Invalid GitHub API key format',
                'pattern': r'^ghp_[a-zA-Z0-9]{36}$'
            },
            'HUGGING_FACE_API_KEY': {
                'min_length': 34,
                'err_msg': 'Invalid Hugging Face API key format',
                'pattern': r'^hf_[a-zA-Z0-9]{30,}$'
            }
        }

        for var, rules in required.items():
            value = os.getenv(var)
            if not is_ci:
                if not value:
                    missing.append(var)
                elif len(value) < rules['min_length']:
                    invalid.append(f"{var}: {rules['err_msg']}")
                elif 'pattern' in rules and not re.match(rules['pattern'], value):
                    invalid.append(f"{var}: {rules['err_msg']}")

        if missing:
            logging.error(f"Missing environment variables: {', '.join(missing)}")
            raise ConfigError(f"Missing required environment variables: {', '.join(missing)}")
        if invalid:
            logging.error(f"Validation errors: {', '.join(invalid)}")
            raise ConfigError(f"Validation errors:\n- " + "\n- ".join(invalid))

        return cls

    @classmethod
    def get(cls, var_name: str, default=None):
        value = os.getenv(var_name, default)
        if value is None and default is None:
            logging.error(f"Environment variable {var_name} not found")
            raise ConfigError(f"Environment variable {var_name} not found")
        return value
