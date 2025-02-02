from pydantic import BaseModel, UUID4
from typing import List, Dict, Optional, Any
import uuid

class Edge(BaseModel):
    id: UUID4
    source: UUID4
    target: UUID4
    type: str
    weight: float = 1.0

class Node(BaseModel):
    id: UUID4
    type: str
    content: str
    metadata: Dict[str, Any] = {}
    relationships: List[UUID4] = []

class KnowledgeGraph(BaseModel):
    nodes: Dict[UUID4, Node] = {}
    edges: Dict[UUID4, Edge] = {}
    search_index: Dict[str, List[UUID4]] = {}

    def add_node(self, node: Node) -> UUID4:
        """
        Add a node to the Knowledge Graph.
        """
        node_id = uuid.uuid4()
        node.id = node_id
        self.nodes[node_id] = node
        self._update_search_index(node)
        return node_id

    def get_node(self, node_id: UUID4) -> Optional[Node]:
        """
        Retrieve a node by its ID.
        """
        return self.nodes.get(node_id)

    def add_edge(self, source: UUID4, target: UUID4, edge_type: str, weight: float = 1.0) -> UUID4:
        """
        Add an edge between two nodes.
        """
        edge_id = uuid.uuid4()
        edge = Edge(
            id=edge_id,
            source=source,
            target=target,
            type=edge_type,
            weight=weight
        )
        self.edges[edge_id] = edge
        # Update relationships in source and target nodes
        if source in self.nodes:
            self.nodes[source].relationships.append(edge_id)
        if target in self.nodes:
            self.nodes[target].relationships.append(edge_id)
        return edge_id

    def get_relationships(self, node_id: UUID4, relationship_type: str = None) -> List[Node]:
        """
        Get nodes related to a given node, optionally filtered by relationship type.
        """
        if node_id not in self.nodes:
            return []
        edge_ids = self.nodes[node_id].relationships
        related_nodes = []
        for edge_id in edge_ids:
            edge = self.edges.get(edge_id)
            if edge and (not relationship_type or edge.type == relationship_type):
                target_node = self.get_node(edge.target)
                if target_node:
                    related_nodes.append(target_node)
        return related_nodes

    def search(self, query: str) -> List[Node]:
        """
        Perform a basic semantic search in the Knowledge Graph.
        """
        if not query:
            return []
        keywords = query.lower().split()
        results = []
        # Search in search_index for matching keywords
        for keyword in keywords:
            for node_id in self.search_index.get(keyword, []):
                if node_id not in results:
                    results.append(node_id)
        # Return nodes in order of relevance (number of matching keywords)
        relevance = {}
        for node_id in results:
            node = self.get_node(node_id)
            if node:
                match_count = sum(1 for keyword in keywords if keyword in node.content.lower())
                relevance[node_id] = match_count
        # Sort by relevance
        sorted_node_ids = sorted(relevance.keys(), key=lambda x: relevance[x], reverse=True)
        return [self.get_node(node_id) for node_id in sorted_node_ids if self.get_node(node_id)]

    def _update_search_index(self, node: Node) -> None:
        """
        Update the search index with the content of the node.
        """
        words = node.content.lower().split()
        for word in words:
            if word not in self.search_index:
                self.search_index[word] = []
            if node.id not in self.search_index[word]:
                self.search_index[word].append(node.id)

def initialize_knowledge_graph() -> KnowledgeGraph:
    """
    Initialize the Knowledge Graph with example data.
    """
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
