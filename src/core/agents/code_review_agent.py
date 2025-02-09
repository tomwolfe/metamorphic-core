# File: src/core/agents/code_review_agent.py
from src.core.knowledge_graph import KnowledgeGraph
import subprocess
import tempfile
import re
import logging
from datetime import datetime

logger = logging.getLogger(__name__)

class CodeReviewAgent:
    def __init__(self, kg: KnowledgeGraph):
        self.kg = kg
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
        node = {
            'type': 'code_review',
            'content': 'Static analysis findings from flake8',
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
