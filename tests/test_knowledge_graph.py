from src.core.knowledge_graph import KnowledgeGraph, Node, initialize_knowledge_graph
from pydantic import UUID4
import pytest

def test_add_and_retrieve_node():
    kg = KnowledgeGraph()
    node_id = kg.add_node(Node(
        type="test",
        content="test content"
    ))
    retrieved_node = kg.get_node(node_id)
    assert retrieved_node is not None
    assert retrieved_node.content == "test content"

def test_search_functionality():
    kg = initialize_knowledge_graph()
    results = kg.search("Hello")
    assert len(results) > 0
    assert any("Hello" in node.content for node in results)

    # Test context chunk search
    context_chunk_id = kg.add_node(Node(type="context_chunk", content="test search"))
    context_chunk = kg.get_node(context_chunk_id)
    search_results = kg.search("test")
    assert any(str(context_chunk.id) in str(node.id) for node in search_results)

def test_relationships():
    kg = initialize_knowledge_graph()
    # Find the hello_world node by content
    hello_world = next(node for node in kg.nodes.values() if node.content == "print('Hello, world!')")
    related_nodes = kg.get_relationships(hello_world.id, "related_to")
    assert len(related_nodes) == 1
    assert related_nodes[0].type == "ethical_principle"

def test_context_chunk_relationships():
    kg = initialize_knowledge_graph()
    chunk = "print('Hello, world!')"
    chunk_node = Node(type="context_chunk", content=chunk)
    chunk_id = kg.add_node(chunk_node)
    summary_node = Node(type="context_summary", content="Summary of chunk")
    summary_id = kg.add_node(summary_node)

    # Check relationships
    edge_id = kg.add_edge(chunk_id, summary_id, "has_summary")
    assert edge_id is not None