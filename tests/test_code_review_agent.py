# File: tests/test_code_review_agent.py
import pytest
from src.core.agents.code_review_agent import CodeReviewAgent
from src.core.knowledge_graph import KnowledgeGraph

@pytest.fixture
def review_agent():
    return CodeReviewAgent(KnowledgeGraph())

def test_parse_flake8_output(review_agent):
    sample_output = '''test.py:1:1: E302 expected 2 blank lines, found 1
test.py:3:5: F401 'os' imported but unused'''
    
    results = review_agent._parse_results(sample_output)
    assert len(results['static_analysis']) == 2
    assert results['static_analysis'][0]['code'] == 'E302'
