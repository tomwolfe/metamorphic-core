# src/core/agents/code_review_agent.py
from src.core.knowledge_graph import KnowledgeGraph, Node
import subprocess
import tempfile
import re
import json
import logging
import os
from datetime import datetime

logger = logging.getLogger(__name__)

class CodeReviewAgent:
    def __init__(self, kg: KnowledgeGraph=None):
        self.kg = kg if kg is not None else KnowledgeGraph()
        # Corrected regex from LLM Solution 2
        self.issue_pattern = re.compile(
            r"^(?P<file>.+):(?P<line>\d+):(?P<col>\d+): (?P<code>\w+) (?P<message>.+)$"
        )

    def analyze_python(self, code: str) -> dict:
        """Analyze Python code using Flake8 (MVP only)."""
        flake8_results = {'static_analysis': [], 'output': ''}
        # bandit_results = {'findings': [], 'error': False, 'error_message': None}  # Initialize bandit_results - Commented out for MVP

        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=True) as tmp:
                os.chmod(tmp.name, 0o600)
                tmp.write(code)
                tmp.flush()
                try:
                    result_flake8 = subprocess.run(
                        ['flake8', tmp.name],
                        capture_output=True,
                        text=True,
                        check=False  # Changed to avoid raising exceptions
                    )
                    flake8_output = result_flake8.stdout.strip() # Keep output parsing

                    # Return structured dict including output and parsed findings
                    return {
                        'output': flake8_output,
                        'static_analysis': self._parse_flake8_results(flake8_output) # Parse results
                    }

                except FileNotFoundError as e:
                    logger.error(f"Flake8 executable not found: {str(e)}")
                    return {'error': f"FileNotFoundError: {str(e)}", 'static_analysis': []} # Include static_analysis empty list in error case

        except Exception as e:
            logger.error(f"Unexpected error during code analysis: {str(e)}")
            return {'error': f"Unexpected error: {str(e)}", 'static_analysis': []} # Include static_analysis empty list in exception case

    def _parse_flake8_results(self, output: str) -> list: # Return type is list of findings
        """Parse Flake8 output into structured findings."""
        findings = []
        for line in output.splitlines():
            match = self.issue_pattern.match(line)
            if match:
                details = match.groupdict()
                details["severity"] = self._determine_severity(details["code"])
                findings.append(details)
        return findings

    def _determine_severity(self, code: str) -> str:
        """Map Flake8 error codes to severity levels."""
        severity_map = {
            'E': 'error',
            'F': 'error',
            'W': 'warning',
            'C': 'warning',
            'S': 'security', # Although 'S' is not flake8 standard, kept for potential extensions
            'B9': 'security', # Although 'B9' is not flake8 standard, kept for potential extensions
            'PL': 'style',     # Pylint - example for future plugins
            'D': 'info',      # Documentation (pydocstyle)
            'N': 'info',      # Naming conventions
            'T': 'info'       # Type hints
        }
        return severity_map.get(code[0], 'info') # Default to 'info' if not in map

