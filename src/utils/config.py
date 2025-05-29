import os
import logging
from dotenv import load_dotenv
import re # Keep re for API key validation
from typing import TypeVar, Union, Any # For generic type hinting in get()

T = TypeVar('T') # For generic type hinting in get()

class ConfigError(Exception):
    pass

class SecureConfig:
    _parsed_config = {}
    _config_loaded_and_validated = False # Flag to ensure load() runs once effectively

    @classmethod
    def load(cls):
        if cls._config_loaded_and_validated:
            return cls

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
        if invalid and not is_ci: # Only raise for invalid API keys if not in CI
            logging.error(f"Validation errors: {', '.join(invalid)}")
            raise ConfigError(f"Validation errors:\n- " + "\n- ".join(invalid))

        # Parse ENABLE_HUGGING_FACE
        enable_hf_str = os.getenv("ENABLE_HUGGING_FACE", "true").lower()
        if enable_hf_str in ["true", "1", "yes", "on"]:
            cls._parsed_config["ENABLE_HUGGING_FACE"] = True
        elif enable_hf_str in ["false", "0", "no", "off"]:
            cls._parsed_config["ENABLE_HUGGING_FACE"] = False
        else:
            logging.warning(f"Invalid value for ENABLE_HUGGING_FACE: '{os.getenv('ENABLE_HUGGING_FACE')}'. Defaulting to true.")
            cls._parsed_config["ENABLE_HUGGING_FACE"] = True

        # Parse LLM_MAX_RETRIES
        try:
            cls._parsed_config["LLM_MAX_RETRIES"] = int(os.getenv("LLM_MAX_RETRIES", "3"))
        except ValueError:
            logging.warning("Invalid integer value for LLM_MAX_RETRIES. Defaulting to 3.")
            cls._parsed_config["LLM_MAX_RETRIES"] = 3

        # Parse LLM_TIMEOUT
        try:
            cls._parsed_config["LLM_TIMEOUT"] = int(os.getenv("LLM_TIMEOUT", "30"))
        except ValueError:
            logging.warning("Invalid integer value for LLM_TIMEOUT. Defaulting to 30.")
            cls._parsed_config["LLM_TIMEOUT"] = 30

        cls._config_loaded_and_validated = True
        return cls

    @classmethod
    def get(cls, var_name: str, default: T = None) -> Union[T, str, None]:
        if not cls._config_loaded_and_validated:
            cls.load() # Ensure configuration is loaded

        if var_name in cls._parsed_config:
            return cls._parsed_config[var_name]

        env_value_str = os.getenv(var_name)

        if env_value_str is not None:
            if default is not None: # Attempt type conversion if default is provided
                if isinstance(default, bool):
                    if env_value_str.lower() in ["true", "1", "yes", "on"]: return True
                    if env_value_str.lower() in ["false", "0", "no", "off"]: return False
                    logging.warning(f"Invalid boolean value for {var_name}: '{env_value_str}'. Using default: {default}")
                    return default
                elif isinstance(default, int):
                    try:
                        return int(env_value_str)
                    except ValueError:
                        logging.warning(f"Invalid integer value for {var_name}: '{env_value_str}'. Using default: {default}")
                        return default
                # Add other type conversions (e.g., float) here if needed
            return env_value_str # Return as string if no default type hint or conversion failed

        # env_value_str is None (variable not in environment)
        if default is not None:
            return default

        # Variable not in environment, not pre-parsed, and no default provided to get()
        # This implies it's a variable expected to be set if used without a default.
        # API keys are validated in load(), so this path is for other potentially critical configs.
        logging.error(f"Configuration variable '{var_name}' not found and no default was provided.")
        raise ConfigError(f"Configuration variable '{var_name}' not found.")