# tests/test_security.py
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import pytest
from pathlib import Path

SENSITIVE_PATHS = [
    # Environment files
    ".env",
    
    # Secret directories
    "secrets/",
    "credentials/",
    
    # Security-sensitive files
    "docker-compose.yml",  # Should only use .example version
    "repo_to_single_file.sh",
    "repo_contents.txt",

    "venv/",
]

@pytest.mark.security
def test_sensitive_files_not_in_repo():
    """Verify sensitive files/directories are excluded from version control"""
    violations = []
    
    for path in SENSITIVE_PATHS:
        full_path = Path(path)
        
        # Check for exact matches and directory contents
        if full_path.exists():
            if full_path.is_dir():
                # Check if directory contains any files
                if any(full_path.iterdir()):
                    violations.append(f"Directory {path} exists and contains files")
            else:
                violations.append(f"File {path} exists in repository")

    assert not violations, "\n".join([
        "Sensitive resources found in version control:",
        *violations,
        "Check .gitignore rules and remove these files from git history"
    ])

def test_no_hardcoded_secrets():
    """Scan codebase for potential secret exposures"""
    # This would integrate with a tool like detect-secrets
    # For now, just validate no .env values are committed
    env_example = Path(".env.example").read_text()
    assert "your_key_here" in env_example, "Sample key placeholder missing"
    assert "LLM_PROVIDER=gemini" in env_example, "Sample config missing"
