# File: src/core/agents/code_review_agent.py
import subprocess
from typing import Dict
from src.core.knowledge_graph import KnowledgeGraph, Node

class CodeReviewAgent:
    def __init__(self):
        self.kg = KnowledgeGraph()
        
    def analyze_code(self, code_path: str) -> Dict:
        result = subprocess.run(['flake8', code_path], capture_output=True)
        return {
            'issues': result.stdout.decode().splitlines(),
            'score': 100 - min(len(result.stdout.decode().splitlines()), 100)
        }
