# File: src/core/agents/code_review_agent.py
from src.core.knowledge_graph import KnowledgeGraph
import subprocess
import tempfile
import re
import logging  # Import logging

logger = logging.getLogger(__name__)  # Get logger instance

class CodeReviewAgent:
    def __init__(self, kg: KnowledgeGraph):
        self.kg = kg
        self.issue_pattern = re.compile(
            r"(?P<file>.+):(?P<line>\d+):(?P<col>\d+): (?P<code>\w+) (?P<msg>.+)")

    def analyze_python(self, code: str) -> dict:
        try:  # Add try-except block
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py') as tmp:
                tmp.write(code)
                tmp.flush()
                result = subprocess.run(
                    ['flake8', tmp.name],
                    capture_output=True,
                    text=True,
                    check=True  # Ensure CalledProcessError is raised for non-zero exit codes
                )
                return self._parse_results(result.stdout)
        except subprocess.CalledProcessError as e:  # Catch CalledProcessError
            logger.error(f"Flake8 analysis failed with return code: {e.returncode}")  # Log error
            logger.error(f"Flake8 stderr: {e.stderr}")  # Log stderr
            return {
                'error': True,  # Indicate error
                'error_message': f"Flake8 analysis failed: {e}",  # Include error message
                'static_analysis': []  # Return empty list for findings
            }
        except FileNotFoundError as e: # Catch FileNotFoundError specifically for flake8 not being installed
            logger.error(f"Flake8 executable not found: {str(e)}")  # Log specific FileNotFoundError
            return {
                'error': True,  # Indicate error
                'error_message': f"Flake8 executable not found: {str(e)}",  # Include error message
                'static_analysis': []  # Return empty list for findings
            }
        except Exception as e:  # Catch other exceptions as well
            logger.error(f"Error running flake8: {str(e)}")  # Log general error
            return {
                'error': True,  # Indicate error
                'error_message': f"Error running flake8: {str(e)}",  # Include error message
                'static_analysis': []  # Return empty list for findings
            }

    def store_findings(self, findings: dict, code_hash: str):
        node = {
            'type': 'code_review',
            'content': 'Static analysis findings',
            'metadata': {
                'code_hash': code_hash,
                'findings': findings['static_analysis'],
                'timestamp': datetime.utcnow().isoformat()
            }
        }
        self.kg.add_node(node)

    def _parse_results(self, output: str) -> dict:
        findings = []
        for match in self.issue_pattern.finditer(output):
            findings.append(match.groupdict())
        return {'static_analysis': findings}
