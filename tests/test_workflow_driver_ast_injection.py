# tests/test_workflow_driver_ast_injection.py

import pytest
import ast
from pathlib import Path
from unittest.mock import patch, MagicMock, ANY
from src.core.automation.workflow_driver import WorkflowDriver, Context

@pytest.fixture
def driver_for_ast_tests(tmp_path, mocker):
    """Fixture for testing AST-based modifications in WorkflowDriver."""
    context = Context(str(tmp_path))
    mocker.patch.object(WorkflowDriver, '_load_default_policy')
    with patch('src.core.automation.workflow_driver.EnhancedLLMOrchestrator'):
        driver = WorkflowDriver(context)
    driver.llm_orchestrator = MagicMock()
    driver.logger = MagicMock()
    # Mock the full loop dependencies to isolate the step execution logic
    mocker.patch.object(driver, '_update_task_status_in_roadmap')
    mocker.patch.object(driver, 'generate_grade_report')
    mocker.patch.object(driver, '_parse_and_evaluate_grade_report', return_value={"recommended_action": "Completed"})

    # --- FIX: Set roadmap_path for autonomous_loop ---
    driver.roadmap_path = str(tmp_path / "ROADMAP.json") # A dummy path is sufficient
    # --- END FIX ---
    return driver

def test_ast_attribute_injection_simple_init(driver_for_ast_tests, tmp_path, mocker):
    """Tests adding an attribute to a simple __init__ method."""
    driver = driver_for_ast_tests
    source_code = "class MyClass:\n    def __init__(self):\n        self.existing_attr = True\n"
    target_file = tmp_path / "my_class.py"
    target_file.write_text(source_code)

    task = {'task_id': 'ast_test_1', 'status': 'Not Started', 'target_file': str(target_file)}
    plan = ["add an instance attribute `self.new_attr = {}` in the `__init__` method"]

    mocker.patch.object(driver, 'select_next_task', side_effect=[task, None])
    mocker.patch.object(driver, 'generate_solution_plan', return_value=plan)
    mocker.patch.object(driver, 'load_roadmap', return_value=[task])

    driver.autonomous_loop()

    modified_code = target_file.read_text()
    tree = ast.parse(modified_code)
    init_node = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == "__init__"][0]
    
    assert len(init_node.body) == 2
    last_statement = init_node.body[-1]
    assert isinstance(last_statement, ast.Assign)
    assert last_statement.targets[0].attr == "new_attr"
    assert isinstance(last_statement.value, ast.Dict)

def test_ast_attribute_injection_with_pass(driver_for_ast_tests, tmp_path, mocker):
    """Tests adding an attribute to an __init__ method that only contains 'pass'."""
    driver = driver_for_ast_tests
    source_code = "class MyClass:\n    def __init__(self):\n        pass\n"
    target_file = tmp_path / "my_class_pass.py"
    target_file.write_text(source_code)

    task = {'task_id': 'ast_test_2', 'status': 'Not Started', 'target_file': str(target_file)}
    plan = ["add an instance attribute `self.data = []` in the `__init__` method"]

    mocker.patch.object(driver, 'select_next_task', side_effect=[task, None])
    mocker.patch.object(driver, 'generate_solution_plan', return_value=plan)
    mocker.patch.object(driver, 'load_roadmap', return_value=[task])

    driver.autonomous_loop()

    modified_code = target_file.read_text()
    tree = ast.parse(modified_code)
    init_node = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == "__init__"][0]
    
    assert len(init_node.body) == 2
    assert isinstance(init_node.body[0], ast.Pass)
    assert isinstance(init_node.body[1], ast.Assign)
    assert init_node.body[1].targets[0].attr == "data"

def test_ast_injection_fails_if_no_init(driver_for_ast_tests, tmp_path, mocker):
    """Tests that the AST injection step fails if the target file has no __init__ method."""
    driver = driver_for_ast_tests
    source_code = "class MyClass:\n    def some_method(self):\n        pass"
    target_file = tmp_path / "no_init.py"
    target_file.write_text(source_code)

    task = {'task_id': 'ast_test_3', 'status': 'Not Started', 'target_file': str(target_file)}
    plan = ["add an instance attribute `self.failed_attr = None` in the `__init__` method"]

    mocker.patch.object(driver, 'select_next_task', side_effect=[task, None])
    mocker.patch.object(driver, 'generate_solution_plan', return_value=plan)
    mocker.patch.object(driver, 'load_roadmap', return_value=[task])

    driver.autonomous_loop()

    assert target_file.read_text() == source_code
    driver._update_task_status_in_roadmap.assert_called_once_with('ast_test_3', 'Blocked', ANY)