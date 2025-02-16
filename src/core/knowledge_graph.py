from pydantic import BaseModel, UUID4
from typing import List, Dict, Optional, Any
import uuid
import re

class Edge(BaseModel):
    id: UUID4
    source: UUID4
    target: UUID4
    type: str
    weight: float = 1.0

class Node(BaseModel):
    id: Optional[UUID4] = None
    type: str
    content: str
    metadata: Dict[str, Any] = {}
    relationships: List[UUID4] = []

class KnowledgeGraph(BaseModel):
    nodes: Dict[UUID4, Node] = {}
    edges: Dict[UUID4, Edge] = {}
    search_index: Dict[str, List[UUID4]] = {}

    def add_node(self, node: Node) -> UUID4:
        if not node.id:
            node.id = uuid.uuid4()
        node_id = node.id
        self.nodes[node_id] = node
        self._update_search_index(node)
        return node_id

    def get_node(self, node_id: UUID4) -> Optional[Node]:
        return self.nodes.get(node_id)

    def add_edge(self, source: UUID4, target: UUID4, edge_type: str, weight: float = 1.0) -> UUID4:
        edge_id = uuid.uuid4()
        edge = Edge(
            id=edge_id,
            source=source,
            target=target,
            type=edge_type,
            weight=weight
        )
        self.edges[edge_id] = edge
        if source in self.nodes:
            self.nodes[source].relationships.append(edge_id)
        if target in self.nodes:
            self.nodes[target].relationships.append(edge_id)
        return edge_id

    def get_relationships(self, node_id: UUID4, relationship_type: str = None) -> List[Node]:
        if node_id not in self.nodes:
            return []
        edge_ids = self.nodes[node_id].relationships
        related_nodes = []
        for edge_id in edge_ids:
            edge = self.edges.get(edge_id)
            if edge is None:
                continue
            if relationship_type and edge.type != relationship_type:
                continue
            if edge.source == node_id:
                related_node_id = edge.target
            elif edge.target == node_id:
                related_node_id = edge.source
            else:
                continue
            related_node = self.get_node(related_node_id)
            if related_node:
                related_nodes.append(related_node)
        return related_nodes


    def search(self, query: str) -> List[Node]:
        if not query:
            return []
        keywords = query.lower().split()
        results = []
        for keyword in keywords:
            for node_id in self.search_index.get(keyword, []):
                if node_id not in results:
                    results.append(node_id)
        relevance = {}
        for node_id in results:
            node = self.get_node(node_id)
            if node:
                match_count = sum(1 for kw in keywords if kw in self.search_index.get(kw, []))
                relevance[node_id] = match_count
        sorted_node_ids = sorted(relevance.keys(), key=lambda x: relevance[x], reverse=True)
        return [self.get_node(nid) for nid in sorted_node_ids if self.get_node(nid)]

    def _update_search_index(self, node: Node) -> None:
        content = node.content.lower()
        words = re.findall(r"\b\w+\b", content)
        for word in words:
            if word not in self.search_index:
                self.search_index[word] = []
            if node.id not in self.search_index[word]:
                self.search_index[word].append(node.id)

def initialize_knowledge_graph() -> KnowledgeGraph:
    kg = KnowledgeGraph()
    transparency = kg.add_node(Node(
        type="ethical_principle",
        content="Systems must be transparent to users and stakeholders."
    ))
    fairness = kg.add_node(Node(
        type="ethical_principle",
        content="Systems must treat all users fairly and without bias."
    ))
    no_bias = kg.add_node(Node(
        type="constraint",
        content="Avoid introducing systemic bias into algorithms."
    ))
    encrypt_data = kg.add_node(Node(
        type="constraint",
        content="Encrypt all sensitive user data."
    ))
    hello_world = kg.add_node(Node(
        type="code_example",
        content="print('Hello, world!')",
        metadata={
            "language": "Python",
            "description": "A basic 'Hello, world!' example."
        }
    ))
    kg.add_edge(transparency, hello_world, "related_to")
    kg.add_edge(no_bias, hello_world, "applies_to")
    return kg
