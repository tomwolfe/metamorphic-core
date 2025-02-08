# File: src/core/agents/specification_analyzer.py
from src.core.knowledge_graph import KnowledgeGraph, Node
from typing import Dict, Any
import ast

class SpecificationAnalyzer:
    def __init__(self, kg: KnowledgeGraph):
        self.kg = kg  # Not 'knowledge_graph' - update test
        
    def analyze_python_spec(self, code: str) -> Dict[str, Any]:
        """Enhanced AST analysis with KG integration"""
        try:
            tree = ast.parse(code)
            analysis = {
                "functions": [],
                "classes": [],
                "imports": []
            }
            
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef):
                    analysis["functions"].append(node.name)
                elif isinstance(node, ast.ClassDef):
                    analysis["classes"].append(node.name)
                elif isinstance(node, (ast.Import, ast.ImportFrom)):
                    analysis["imports"].extend(alias.name for alias in node.names)
            
            self._store_analysis(analysis)
            return analysis
            
        except SyntaxError as e:
            return {"error": str(e)}
            
    def _store_analysis(self, analysis: dict) -> None:
        """Store analysis results in Knowledge Graph"""
        spec_node = Node(
            type="spec_analysis",
            content="Code specification analysis",
            metadata=analysis
        )
        self.kg.add_node(spec_node)
