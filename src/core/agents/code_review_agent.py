# File: src/core/agents/code_review_agent.py
from src.core.knowledge_graph import KnowledgeGraph
import subprocess
import tempfile
import re

class CodeReviewAgent:
    def __init__(self, kg: KnowledgeGraph):
        self.kg = kg
        self.issue_pattern = re.compile(
            r"(?P<file>.+):(?P<line>\d+):(?P<col>\d+): (?P<code>\w+) (?P<msg>.+)")

    def analyze_python(self, code: str) -> dict:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py') as tmp:
            tmp.write(code)
            tmp.flush()
            result = subprocess.run(
                ['flake8', tmp.name], 
                capture_output=True, 
                text=True
            )
            return self._parse_results(result.stdout)

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
