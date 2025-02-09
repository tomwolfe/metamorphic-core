# src/core/agents/code_review_agent.py
# File: src/core/agents/code_review_agent.py
from src.core.knowledge_graph import KnowledgeGraph, Node
import subprocess
import tempfile
import re
import logging
from datetime import datetime

logger = logging.getLogger(__name__)

class CodeReviewAgent:
    def __init__(self, kg: KnowledgeGraph=None): # Added default None for kg for easier instantiation in some contexts
        self.kg = kg if kg is not None else KnowledgeGraph() # Initialize KG if not provided
        self.issue_pattern = re.compile(
            r"(?P<file>.+):(?P<line>\d+):(?P<col>\d+): (?P<code>\w+) (?P<msg>.+)")

    def analyze_python(self, code: str) -> dict:
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py') as tmp:
                tmp.write(code)
                tmp.flush()
                result = subprocess.run(
                    ['flake8', tmp.name],
                    capture_output=True,
                    text=True,
                    check=True
                )
                parsed_results = self._parse_results(result.stdout)

                if not parsed_results.get('error') and parsed_results['static_analysis']:
                    code_hash = hash(code)
                    self.store_findings(parsed_results, str(code_hash))

                return parsed_results

        except subprocess.CalledProcessError as e:
            logger.error(f"Flake8 analysis failed with return code: {e.returncode}")
            logger.error(f"Flake8 stderr: {e.stderr}")
            return {
                'error': True,
                'error_message': f"Flake8 analysis failed: {e}",
                'static_analysis': []
            }
        except FileNotFoundError as e:
            logger.error(f"Flake8 executable not found: {str(e)}")
            return {
                'error': True,
                'error_message': f"Flake8 executable not found: {str(e)}",
                'static_analysis': []
            }
        except Exception as e:
            logger.error(f"Error running flake8: {str(e)}")
            return {
                'error': True,
                'error_message': f"Error running flake8: {str(e)}",
                'static_analysis': []
            }

    def store_findings(self, findings: dict, code_hash: str):
        """Store static analysis findings in the Knowledge Graph."""
        node = Node(
            type="code_review",
            content="Static analysis findings from flake8 with severity", # Updated content for clarity
            metadata={
                "code_hash": code_hash,
                "findings": [{**f, 'severity': f.get('severity', 'unknown')} for f in findings['static_analysis']], # Add severity to each finding
                "timestamp": datetime.utcnow().isoformat()
            }
        )
        self.kg.add_node(node)

    def _parse_results(self, output: str) -> dict:
        findings = []
        severity_map = {
            'E': 'error',          # General Errors
            'F': 'error',          # Fatal errors
            'W': 'warning',        # Warnings
            'C': 'warning',        # Conventions (potential issues)
            'E001': 'style',       # Flake8 E001: Whitespace error
            'E002': 'style',       # Flake8 E002: Continuation line indentation
            'E123': 'style',       # Flake8 E123: Indentation not a multiple of four
            'E1': 'style', 'W6': 'style',  # PEP8 style (example subsets)
            'E2': 'style', 'E3': 'style', 'E4': 'style', 'E5': 'style',
            'E7': 'style', 'E9': 'style', 'C0': 'style', 'C4': 'style', 'C9': 'style',
        }

        for match in self.issue_pattern.finditer(output):
            issue_details = match.groupdict()
            code = issue_details['code']  # Use full code for specific mapping
            issue_details['severity'] = severity_map.get(code, severity_map.get(code[0], 'info'))
            findings.append(issue_details)
        return {'static_analysis': findings}
