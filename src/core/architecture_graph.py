import json
from typing import Dict, List
from pydantic import BaseModel
import google.generativeai as genai

class ArchitectureNode(BaseModel):
    type: str
    purpose: str
    dependencies: List[str]
    status: str = "proposed"
    spec_priority: int
    implementation_path: str = ""

class ArchitectureGraph:
    def __init__(self, llm_client):
        self.llm = llm_client
        self.graph: Dict[str, ArchitectureNode] = {}
        self._initialize_base_architecture()

    def _initialize_base_architecture(self):
        base_nodes = {
            'code_generation': ArchitectureNode(
                type='component',
                purpose='Generate code from specifications',
                dependencies=[],
                spec_priority=1,
                status='active'
            ),
            'self_improvement': ArchitectureNode(
                type='process',
                purpose='Basic code analysis and patching',
                dependencies=['code_generation'],
                spec_priority=2,
                status='active'
            )
        }
        self.graph.update(base_nodes)

    def get_graph_state(self) -> str:
        return json.dumps(
            {name: node.dict() for name, node in self.graph.items()},
            indent=2
        )

    def determine_next_milestone(self) -> str:
        prompt = f"""Analyze architecture and suggest next component..."""
        return self.llm.generate_content(prompt).text.strip()
