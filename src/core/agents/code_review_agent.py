from src.core.knowledge_graph import KnowledgeGraph, Node
import subprocess
import tempfile
import re
import logging
import os
from datetime import datetime

logger = logging.getLogger(__name__)

class CodeReviewAgent:
    def __init__(self, kg: KnowledgeGraph=None):
        self.kg = kg if kg is not None else KnowledgeGraph()
        self.issue_pattern = re.compile(
            r"(?P<file>.+):(?P<line>\d+):(?P<col>\d+): (?P<code>\w+) (?P<msg>.+)")

    def analyze_python(self, code: str) -> dict:
        flake8_results = {'static_analysis': [], 'output': ''}
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
                    parsed = self._parse_flake8_results(result_flake8.stdout)
                    flake8_results = {
                        'output': result_flake8.stdout,
                        'static_analysis': parsed.get('static_analysis', []),
                        'error': False
                    }
                except FileNotFoundError as e:
                    logger.error(f"Flake8 executable not found: {str(e)}")
                    return {
                        'error': True,
                        'error_message': f"Flake8 executable not found: {str(e)}",
                        'output': "",
                        'static_analysis': []
                    }
                except Exception as e:
                    logger.error(f"Error running flake8: {str(e)}")
                    return {
                        'error': True,
                        'error_message': f"Error running flake8: {str(e)}",
                        'output': "",
                        'static_analysis': []
                    }

                return flake8_results

        except Exception as e:
            logger.error(f"Unexpected error during code analysis: {str(e)}")
            return {
                'error': True,
                'error_message': f"Unexpected error during code analysis: {str(e)}",
                'output': "",
                'static_analysis': []
            }

    def _parse_flake8_results(self, output: str) -> dict:
        findings = []
        for match in self.issue_pattern.finditer(output):
            issue_details = match.groupdict()
            issue_details['severity'] = self._determine_severity(issue_details['code'])
            findings.append(issue_details)
        return {'static_analysis': findings}

    def _determine_severity(self, code: str) -> str:
        severity_map = {
            'E': 'error',
            'F': 'error',
            'W': 'warning',
            'C': 'warning',
            'S': 'security',
            'B9': 'security',  
        }
        return severity_map.get(code[0], 'info')
