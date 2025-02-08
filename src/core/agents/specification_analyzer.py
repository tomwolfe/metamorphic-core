from src.core.knowledge_graph import KnowledgeGraph
import ast

class SpecificationAnalyzer:
    def __init__(self, kg: KnowledgeGraph):
        self.kg = kg
        
    def analyze_python_spec(self, code: str) -> dict:
        """Analyze Python code specifications using AST"""
        try:
            tree = ast.parse(code)
            return {
                "functions": len([n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]),
                "classes": len([n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]),
                "imports": len([n for n in ast.walk(tree) if isinstance(n, ast.Import|ast.ImportFrom)])
            }
        except SyntaxError as e:
            return {"error": str(e)}
