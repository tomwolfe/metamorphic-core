# File: src/core/automation/workflow_driver.py
import logging
import html
import os
import json
from pathlib import Path
from src.core.llm_orchestration import EnhancedLLMOrchestrator
import re
from unittest.mock import MagicMock # Keep MagicMock for other dependencies if needed
from src.cli.write_file import write_file # Ensure write_file is imported
import subprocess # Import subprocess for execute_tests
from src.core.agents.code_review_agent import CodeReviewAgent # Import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine # Import EthicalGovernanceEngine
from datetime import datetime # Import datetime for report timestamp
import uuid # Import uuid for temporary file naming
import builtins # Import builtins for mocking open

# Use name for the logger name
logger = logging.getLogger(__name__) # Corrected logger name

# Define a maximum file size for reading (e.g., 1MB)
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"

class Context:
    def __init__(self, base_path):
        self.base_path = base_path
        # Resolve base_path immediately for safety checks
        try:
            self._resolved_base_path = Path(self.base_path).resolve()
        except Exception as e:
            logger.error(f"Error resolving base path '{self.base_path}': {e}", exc_info=True)
            self._resolved_base_path = None # Indicate resolution failure


    def get_full_path(self, relative_path):
        """Resolves a relative path against the context's base path."""
        if self._resolved_base_path is None:
            logger.error(f"Base path failed to resolve. Cannot resolve relative path '{relative_path}'.")
            return None

        if not isinstance(relative_path, str) or relative_path == "": # Added check for empty string
            # Handle non-string or empty input gracefully
            # An empty string relative path should resolve to the base path itself
            if relative_path == "":
                return str(self._resolved_base_path)
            logger.warning(f"Attempted to resolve path with invalid input: {relative_path}")
            return None

        try:
            # Resolve the requested path relative to the base path
            full_requested_path = self._resolved_base_path / relative_path
            resolved_path = full_requested_path.resolve()

            # Check if the resolved path starts with the resolved base path
            # This prevents '..' traversal and absolute paths resolving outside the base
            if not str(resolved_path).startswith(str(self._resolved_base_path)):
                logger.warning(f"Path traversal attempt detected during resolution: {relative_path} resolved to {resolved_path}")
                return None # Return None if path resolves outside the base directory

            return str(resolved_path)
        except Exception as e:
            logger.error(f"Error resolving path '{relative_path}' relative to '{self.base_path}': {e}", exc_info=True)
            return None


    def __eq__(self, other):
        """Compares two Context objects based on their base_path."""
        if not isinstance(other, Context):
            return NotImplemented
        return self.base_path == other.base_path

    def __repr__(self):
        return f"Context(base_path='{self.base_path}')"

class WorkflowDriver:
    def __init__(self, context: Context):
        self.context = context
        self.tasks = [] # Will be loaded by start_workflow
        self._current_task_results = {} # Dictionary to store results for the current task iteration
        self.remediation_attempts = 0 # Initialize remediation counter


        # Instantiate EthicalGovernanceEngine and load default policy FIRST
        self.ethical_governance_engine = EthicalGovernanceEngine()
        self._load_default_policy() # Extract policy loading to a separate method

        # Initialize LLM Orchestrator - Pass REAL dependencies where available
        # Pass the real ethical_governance_engine instance
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(), # Assuming KG is still mocked for now
            spec=MagicMock(), # Assuming Spec is still mocked for now
            ethics_engine=self.ethical_governance_engine # <--- Pass the REAL instance here
        )
        # Instantiate CodeReviewAgent
        self.code_review_agent = CodeReviewAgent()


    def _load_default_policy(self):
        """Load the default ethical policy from file."""
        # Use context.get_full_path for safety when loading the policy file
        default_policy_path = self.context.get_full_path("policies/policy_bias_risk_strict.json")
        if default_policy_path:
            try:
                with builtins.open(default_policy_path, 'r') as f: # Use builtins.open
                     self.default_policy_config = json.load(f) # Use json.load
                logger.info(f"Loaded default ethical policy: {self.default_policy_config.get('policy_name')}")
            except FileNotFoundError:
                 logger.warning(f"Default ethical policy file not found at {default_policy_path}. Ethical analysis will be skipped.")
                 self.default_policy_config = None
            except json.JSONDecodeError:
                 logger.error(f"Invalid JSON in default ethical policy file: {default_policy_path}. Ethical analysis will be skipped.")
                 self.default_policy_config = None
            except Exception as e:
                logger.error(f"Failed to load default ethical policy from {default_policy_path}: {e}", exc_info=True)
                self.default_policy_config = None # Set to None if loading fails
        else:
            logger.warning("Could not resolve path for default ethical policy. Ethical analysis may be impacted.")
            self.default_policy_config = None


    def start_workflow(self, roadmap_path: str, output_dir: str, context: Context):
        """
        Initiates the autonomous workflow loop with specific context.

        Args:
            roadmap_path: Path to the roadmap JSON file.
            output_dir: Path to the output directory.
            context: The Context object for the workflow.
        """
        self.roadmap_path = roadmap_path
        self.output_dir = output_dir  # Store output_dir for potential future use

        # Load the roadmap once at the start of the workflow
        try:
            # Use the context's get_full_path for safety when loading the roadmap
            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
            if full_roadmap_path is None:
                logger.error(f"Invalid roadmap path provided: {self.roadmap_path}")
                return # Exit if roadmap path is invalid after resolving
            self.tasks = self.load_roadmap(full_roadmap_path) # Load from the resolved path
        except Exception as e:
            logger.error(f"Failed to reload roadmap from {self.roadmap_path}: {e}",
                         exc_info=True)
            # This break was inside the while loop in the original code,
            # but start_workflow should just return on failure.
            return # Exit if roadmap loading fails
        self.context = context  # Update context if needed (though it's set in __init__)
        logger.info(f"Workflow initiated with roadmap: {roadmap_path}, output: {output_dir}")
        self.autonomous_loop()

    def autonomous_loop(self):
        """
        Main control flow loop for the autonomous Driver LLM.

        This method orchestrates the task selection, planning, agent invocation,
        and file management steps to drive the development process autonomously.
        """
        # Ensure roadmap_path is set before trying to load
        if not hasattr(self, 'roadmap_path') or (self.roadmap_path is None): # Check for None explicitly
            logger.error("Roadmap path not set. Cannot start autonomous loop.")
            return # Exit if roadmap path is not set

        MAX_REMEDIATION_ATTEMPTS = 2 # Define max attempts here

        while True:
            logger.info('Starting autonomous loop iteration')
            self._current_task_results = {} # Reset results for the new task iteration
            self.remediation_occurred_in_pass = False # Flag to track if *any* remediation attempt in this pass succeeded in writing

            # Load the roadmap inside the loop to get the latest status updates
            try:
                full_roadmap_path = self.context.get_full_path(self.roadmap_path)
                if full_roadmap_path is None:
                    logger.error(f"Invalid roadmap path provided: {self.roadmap_path}. Cannot continue autonomous loop.")
                    break # Exit loop if roadmap path is invalid
                self.tasks = self.load_roadmap(full_roadmap_path)
            except Exception as e:
                logger.error(f"Failed to reload roadmap from {self.roadmap_path}: {e}",
                             exc_info=True)
                break # Exit loop if roadmap reloading fails

            next_task = self.select_next_task(self.tasks)

            if next_task:
                task_id = next_task.get('task_id', 'Unknown ID')
                logger.info(f'Selected task: ID={task_id}')

                solution_plan = self.generate_solution_plan(next_task)
                logger.info(f'Generated plan: {solution_plan}')

                if solution_plan:
                    logger.info(
                        f"Executing plan for task {task_id} with {len(solution_plan)} steps.")
                    # Flag to track if any code was written in this iteration
                    code_written_in_iteration = False
                    filepath_to_use = next_task.get('target_file') # Initialize filepath_to_use from task

                    for step_index, step in enumerate(solution_plan):
                        logger.info(f"Executing step {step_index + 1}/{len(solution_plan)}: {step}")

                        step_lower = step.lower()  # Convert step to lower once

                        # Define keywords for step classification
                        code_generation_keywords = ["implement", "generate code",
                                                    "write function", "modify file",
                                                    "add logic to", "define class",
                                                    "create method", "add import",
                                                    "update constant", "refactor"] # Added more keywords
                        file_writing_keywords = ["write file", "create file", "save to file",
                                                 "output file", "generate file", "write output to",
                                                 "update file", "modify file"] # Added "update file", "modify file"
                        test_execution_keywords = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]


                        # --- REVISED LOGIC FOR DETERMINING STEP TYPE AND FILE PATH (PRIORITIZE target_file) ---
                        # This regex is primarily for extracting a filename *if* one is mentioned,
                        # but the logic below will prioritize target_file.
                        filepath_match = re.search(
                            r'(\S+\.(py|md|json|txt|yml|yaml))', step, re.IGNORECASE)
                        filepath_from_step = filepath_match.group(1) if filepath_match else None

                        # Check for keywords indicating code generation
                        is_code_generation_step = any(keyword in step_lower for keyword in code_generation_keywords)

                        # Check for keywords indicating explicit file writing (non-code-gen)
                        # FIX: This flag should ONLY check for file_writing_keywords, not filepath_from_step
                        is_explicit_file_writing_step = any(keyword in step_lower for keyword in file_writing_keywords)

                        # Check for test execution keywords
                        is_test_execution_step = any(keyword in step_lower for keyword in test_execution_keywords)


                        # Determine the actual filepath to use for the operation
                        # Prioritize the target_file from the task metadata
                        # Store this at the task level if not already set
                        if filepath_to_use is None:
                            filepath_to_use = next_task.get('target_file')

                        # If the task doesn't have a target_file, but the step mentions one and is file-related, use the one from the step.
                        # FIX: Only use filepath_from_step if it's an explicit file writing or code generation step AND no target_file is set
                        if not filepath_to_use and (is_explicit_file_writing_step or is_code_generation_step) and filepath_from_step:
                            filepath_to_use = filepath_from_step
                        # --- END REVISED LOGIC ---


                        generated_output = None  # Initialize generated_output for this step
                        content_to_write = None # Initialize content_to_write
                        overwrite_file = False # Initialize overwrite flag

                        # --- START MODIFIED LOGIC FOR STEP PROCESSING (REORDERED) ---
                        # Prioritize test execution steps
                        if is_test_execution_step:
                            logger.info(f"Step identified as test execution. Running tests for step: {step}")
                            test_command = ["pytest"]
                            # FIX: Use filepath_to_use if it looks like a test file, otherwise default to tests/
                            if filepath_to_use and "test_" in Path(filepath_to_use).name.lower():
                                test_command.append(filepath_to_use)
                            else:
                                test_command.append("tests/")

                            try:
                                return_code, stdout, stderr = self.execute_tests(test_command, self.context.base_path)
                                test_results = self._parse_test_results(stdout)
                                self._current_task_results['test_results'] = test_results
                                # FIX: Ensure all keys are present before logging
                                logger.info(f"Test Execution Results: Status={test_results.get('status')}, Passed={test_results.get('passed')}, Failed={test_results.get('failed')}, Total={test_results.get('total')}")
                                if test_results.get('status') == 'failed':
                                    logger.error(f"Tests failed for step: {step}. Raw stderr:\n{stderr}")
                                elif test_results.get('status') == 'error':
                                    logger.error(f"Test execution or parsing error for step: {step}. Message: {test_results.get('message')}. Raw stderr:\n{stderr}")
                            except Exception as e:
                                logger.error(f"An unexpected error occurred during command execution: {e}", exc_info=True)
                                self._current_task_results['test_results'] = {'status': 'error', 'passed': 0, 'failed': 0, 'total': 0, 'message': str(e)}

                        # Prioritize code generation steps targeting a specific file
                        # FIX: Use the new is_code_generation_step flag
                        elif is_code_generation_step and filepath_to_use:
                            logger.info(
                                f"Step identified as code generation for file {filepath_to_use}. Orchestrating read-generate-merge-write.")

                            existing_content = self._read_file_for_context(filepath_to_use)
                            logger.debug(f"Read {len(existing_content)} characters from {filepath_to_use}.")

                            coder_prompt = f"""You are a Coder LLM expert in Python.
Your task is to generate only the code snippet required to implement the following specific step from a larger development plan.

Overall Task: "{next_task.get('task_name', 'Unknown Task')}"
Task Description: {next_task.get('description', 'No description provided.')}

Specific Plan Step:
{step}

The primary file being modified is `{filepath_to_use}`.

EXISTING CONTENT OF `{filepath_to_use}`:
```python
{existing_content}
```

Generate only the Python code snippet needed to fulfill the "Specific Plan Step". Do not include any surrounding text, explanations, or markdown code block fences (```). Provide just the raw code lines that need to be added or modified.
"""
                            logger.debug("Invoking Coder LLM with prompt: %s", coder_prompt[:500])
                            generated_snippet = self._invoke_coder_llm(coder_prompt)


                            if generated_snippet:
                                logger.info(
                                    f"Coder LLM generated snippet (first 100 chars): {generated_snippet[:100]}...")

                                merged_content = self._merge_snippet(existing_content, generated_snippet)
                                logger.debug("Snippet merged.")

                                logger.info(f"Attempting to write merged content to {filepath_to_use}.")
                                try:
                                    self._write_output_file(filepath_to_use, merged_content, overwrite=True)
                                    logger.info(f"Successfully wrote merged content to {filepath_to_use}.")
                                    code_written_in_iteration = True # Mark that code was written

                                    # --- Run Initial Validations after successful write ---
                                    try:
                                        logger.info(f"Running code review and security scan for {filepath_to_use}...")
                                        review_results = self.code_review_agent.analyze_python(merged_content)
                                        self._current_task_results['code_review_results'] = review_results
                                        logger.info(f"Code Review and Security Scan Results for {filepath_to_use}: {review_results}")
                                    except Exception as review_e:
                                        logger.error(f"Error running code review/security scan for {filepath_to_use}: {review_e}", exc_info=True)
                                        self._current_task_results['code_review_results'] = {'status': 'error', 'message': str(review_e)}

                                    if self.default_policy_config:
                                        try:
                                            logger.info(f"Running ethical analysis for {filepath_to_use}...")
                                            ethical_analysis_results = self.ethical_governance_engine.enforce_policy(merged_content, self.default_policy_config)
                                            self._current_task_results['ethical_analysis_results'] = ethical_analysis_results
                                            logger.info(f"Ethical Analysis Results for {filepath_to_use}: {ethical_analysis_results}")
                                        except Exception as ethical_e:
                                            logger.error(f"Error running ethical analysis for {filepath_to_use}: {ethical_e}", exc_info=True)
                                            self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': str(ethical_e)}
                                    else:
                                        logger.warning("Default ethical policy not loaded. Skipping ethical analysis.")
                                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded.'}
                                    # --- END Initial Validations ---

                                except FileExistsError:
                                    logger.error(f"Unexpected FileExistsError when writing merged content to {filepath_to_use} with overwrite=True.")
                                except Exception as e:
                                    logger.error(f"Failed to write merged content to {filepath_to_use}: {e}", exc_info=True)
                            else:
                                logger.warning(f"Coder LLM returned empty or None snippet for step {step_index + 1}. Skipping file write.")

                        # Handle steps identified as file writing, but NOT code generation
                        # This block currently writes placeholder content with overwrite=False
                        # This might need refinement based on whether the step implies creating a *new* file
                        # or modifying an existing one (which would need overwrite=True).
                        # For task_1_8_1, steps modifying workflow_driver.py should use overwrite=True.
                        # FIX: Use the new is_explicit_file_writing_step flag
                        elif is_explicit_file_writing_step and not is_code_generation_step and filepath_to_use:
                            logger.info(f"Step identified as file writing (non-code-gen). Processing file operation for step: {step}")
                            # Determine if this step implies creating a *new* file or modifying an existing one.
                            # Simple heuristic: If the step explicitly says "create file", use overwrite=False.
                            # Otherwise, assume modification and use overwrite=True. This is a simplification.
                            step_implies_create = any(keyword in step_lower for keyword in ["create file", "generate file"])
                            overwrite_mode = not step_implies_create

                            content_to_write = f"// Placeholder content for step: {step}"
                            logger.info(f"Using placeholder content for file: {filepath_to_use} with overwrite={overwrite_mode}")
                            logger.info(f"Attempting to write file: {filepath_to_use}.")
                            try:
                                self._write_output_file(filepath_to_use, content_to_write, overwrite=overwrite_mode)
                                logger.info(f"Successfully wrote placeholder content to {filepath_to_use}.")
                                # Note: Placeholder writes don't trigger validations or remediation in the current logic
                            except FileExistsError:
                                logger.warning(
                                    f"File {filepath_to_use} already exists. Skipping write as overwrite={overwrite_mode}.")
                            except Exception as e:
                                logger.error(f"Failed to write file {filepath_to_use}: {e}",
                                             exc_info=True)

                        # Log if the step was not identified as involving file operations, code generation, or test execution
                        else:
                            # FIX: Updated log message to reflect new flag names and include step description
                            logger.info(
                                f"Step not identified as code generation, explicit file writing, or test execution. Skipping agent invocation/file write for step: {step}")
                        # --- END MODIFIED LOGIC FOR STEP PROCESSING ---

                    # --- Post-Step Execution Logic (Inside the 'if solution_plan:' block) ---
                    # This block runs AFTER all steps in the plan have been attempted.
                    # Phase 1.8 goals (1.8.2, 1.8.3, 1.8.4) suggest moving validation/remediation *inside* the step loop.
                    # The current structure performs validation/remediation *after* the entire plan.
                    # This is a mismatch with the roadmap goals but reflects the current code structure.
                    # The remediation logic below will operate on the *final* state after all steps.

                    logger.info("Generating Grade Report...")
                    # The grade report uses results accumulated across all steps in _current_task_results
                    grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                    logger.info(f"--- GRADE REPORT for Task {task_id} ---\n{grade_report_json}\n--- END GRADE REPORT ---")

                    evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                    recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                    justification = evaluation_result.get("justification", "Evaluation failed.")
                    logger.info(f"Initial Grade Report Evaluation: Recommended Action='{recommended_action}', Justification='{justification}'")

                    # --- BEGIN: Remediation Logic (Currently runs AFTER all steps) ---
                    # Check if remediation is needed based on the initial evaluation
                    # This remediation loop attempts to fix issues based on the *final* state after all steps.
                    # This is different from the step-level remediation described in the roadmap (Task 1.8.3).
                    # This logic needs to be refactored to align with Phase 1.8 goals.
                    if recommended_action == "Regenerate Code":
                        # Check if remediation attempts are available
                        if self.remediation_attempts < MAX_REMEDIATION_ATTEMPTS:
                            logger.info(f"Attempting automated remediation (Attempt {self.remediation_attempts + 1}/{MAX_REMEDIATION_ATTEMPTS})...")
                            self.remediation_occurred_in_pass = False # Flag to track if *any* remediation attempt in this pass succeeded in writing

                            # Read file content once at the start of the remediation pass
                            # This assumes remediation targets the primary file, which might not always be true.
                            # This logic needs refinement for Task 1.8.6.
                            filepath_for_remediation = filepath_to_use # Use the last used filepath or task target
                            if not filepath_for_remediation:
                                logger.error("No target file identified for remediation. Cannot attempt remediation.")
                                # The recommended_action remains "Regenerate Code", but no attempt was made.
                                # The loop will continue, and the task might eventually be marked "Blocked" or require manual review.
                                pass # Continue loop without remediation attempt
                            else:
                                current_file_content = self._read_file_for_context(filepath_for_remediation)

                                if current_file_content:
                                    # --- Attempt Style/Ethical/Test Remediation if applicable ---
                                    # Identify the primary failure type based on the initial report
                                    # This logic needs refinement for Task 1.8.6 to handle multiple issues.
                                    failure_type = self._identify_remediation_target(grade_report_json) # Use the report from the initial evaluation

                                    remediation_attempted = False
                                    remediation_success = False

                                    # Prioritize test failures for remediation (Task 1.8.6)
                                    test_status = self._current_task_results.get('test_results', {}).get('status')
                                    if test_status == 'failed':
                                         remediation_attempted = True
                                         remediation_success = self._attempt_test_failure_remediation(
                                             grade_report_json, next_task, "Test Failure Remediation", filepath_for_remediation, current_file_content
                                         )
                                         if remediation_success:
                                             logger.info("Test failure remediation successful.")
                                             self.remediation_occurred_in_pass = True # Mark that remediation happened
                                             # Re-evaluate immediately after a successful write
                                             grade_report_json = self.generate_grade_report(task_id, self._current_task_results) # Use potentially updated results
                                             logger.info(f"--- REVISED GRADE REPORT (Test Remediation) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                             evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                             recommended_action = evaluation_result.get("recommended_action", "Manual Review Required") # Update action
                                             justification = evaluation_result.get("justification", "Evaluation failed.")
                                             logger.info(f"Revised Grade Report Evaluation (Test Remediation): Recommended Action='{recommended_action}', Justification='{justification}'")
                                         else:
                                             logger.warning("Test failure remediation attempt failed.")


                                    # If test remediation wasn't attempted or failed, try style/ethical if they were the primary identified issue
                                    if not remediation_success and failure_type == "Code Style":
                                        remediation_attempted = True
                                        remediation_success = self._attempt_code_style_remediation(grade_report_json, next_task, "Code Style Remediation", filepath_for_remediation, current_file_content)
                                        if remediation_success:
                                            logger.info("Style remediation attempt seems successful (code written).")
                                            self.remediation_occurred_in_pass = True
                                            # Re-evaluate immediately after a successful write
                                            grade_report_json = self.generate_grade_report(task_id, self._current_task_results) # Use potentially updated results
                                            logger.info(f"--- REVISED GRADE REPORT (Style) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                            evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                            recommended_action = evaluation_result.get("recommended_action", "Manual Review Required") # Update action
                                            justification = evaluation_result.get("justification", "Evaluation failed.")
                                            logger.info(f"Revised Grade Report Evaluation (Style): Recommended Action='{recommended_action}', Justification='{justification}'")
                                        else:
                                            logger.warning("Style remediation attempt failed.")

                                    if not remediation_success and failure_type == "Ethical Transparency":
                                        remediation_attempted = True
                                        remediation_success = self._attempt_ethical_transparency_remediation(grade_report_json, next_task, "Ethical Transparency Remediation", filepath_for_remediation, current_file_content)
                                        if remediation_success:
                                            logger.info("Ethical transparency remediation seems successful (code written).")
                                            self.remediation_occurred_in_pass = True
                                            # Re-evaluate immediately after a successful write
                                            grade_report_json = self.generate_grade_report(task_id, self._current_task_results) # Use potentially updated results
                                            logger.info(f"--- REVISED GRADE REPORT (Ethical) for Task {task_id} ---\n{grade_report_json}\n--- END REVISED GRADE REPORT ---")
                                            evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                            recommended_action = evaluation_result.get("recommended_action", "Manual Review Required") # Update action
                                            justification = evaluation_result.get("justification", "Evaluation failed.")
                                            logger.info(f"Revised Grade Report Evaluation (Ethical): Recommended Action='{recommended_action}', Justification='{justification}'")
                                        else:
                                            logger.warning("Ethical transparency remediation attempt failed.")

                                    # Increment remediation attempts counter *once per pass* if any remediation attempt succeeded in writing
                                    if self.remediation_occurred_in_pass:
                                        self.remediation_attempts += 1
                                        logger.info(f"Remediation attempt {self.remediation_attempts} completed.")
                                    elif remediation_attempted:
                                         logger.warning("Remediation attempt failed to write code.")


                                else: # This else belongs to `if current_file_content:`
                                    logger.error(f"Failed to read current file content for remediation: {filepath_for_remediation}. Cannot attempt remediation.")
                                    # If file read fails, we cannot attempt any code modification remediation.
                                    # The recommended_action remains "Regenerate Code", but no attempt was made.
                                    # The loop will continue, and the task might eventually be marked "Blocked" or require manual review.

                        else: # This else belongs to `if recommended_action == "Regenerate Code":`
                            # This means recommended_action was "Regenerate Code" but attempts were exhausted
                            logger.warning(f"Maximum remediation attempts ({MAX_REMEDIATION_ATTEMPTS}) reached for task {task_id}. Proceeding without further automated remediation.")
                            # The recommended_action remains "Regenerate Code" or whatever the last evaluation set it to.
                            # The loop will continue, potentially leading to Manual Review or Blocked based on the final evaluation.
                    # --- END Remediation Logic ---


                    # --- Update Roadmap Status based on FINAL Evaluation ---
                    # This block should run AFTER all potential remediation attempts for this pass
                    new_status = next_task['status'] # Default to current status
                    if recommended_action == "Completed":
                        new_status = "Completed"
                    elif recommended_action == "Blocked":
                        new_status = "Blocked"
                    # Note: If recommended_action is "Regenerate Code" and attempts are not exhausted,
                    # the status remains 'Not Started' or 'In Progress' (depending on initial state)
                    # and the loop will pick it up again for another attempt.

                    if new_status != next_task['status']:
                        logger.info(f"Updating task status from '{next_task['status']}' to '{new_status}' for task {task_id}")
                        try:
                            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
                            if full_roadmap_path:
                                try:
                                    with builtins.open(full_roadmap_path, 'r') as f:
                                        roadmap_data = json.load(f)
                                except FileNotFoundError:
                                    logger.error(f"Error updating roadmap status for task {task_id}: Roadmap file not found at {full_roadmap_path}")
                                    # Continue loop, but status update failed
                                    continue

                                task_found = False
                                if isinstance(roadmap_data, dict) and isinstance(roadmap_data.get('tasks'), list):
                                    for task_entry in roadmap_data['tasks']:
                                        if isinstance(task_entry, dict) and task_entry.get('task_id') == task_id:
                                            task_entry['status'] = new_status
                                            task_found = True
                                            break

                                if task_found:
                                    if self._safe_write_roadmap_json(self.roadmap_path, roadmap_data):
                                        logger.info(f"Successfully wrote updated status for task {task_id} in {self.roadmap_path}")
                                    else:
                                        logger.error(f"Failed to safely write updated roadmap for task {task_id}")
                                else:
                                    logger.warning(f"Task {task_id} not found in roadmap file {self.roadmap_path} for status update.")
                            else:
                                logger.error(f"Cannot update roadmap status: Invalid roadmap path provided: {self.roadmap_path}")
                        except Exception as e:
                            logger.error(f"Error updating roadmap status for task {task_id}: {e}", exc_info=True)
                    else:
                        logger.info(f"Task status for {task_id} remains '{new_status}' based on evaluation.")
                    # --- END Roadmap Update ---

                else: # This 'else' corresponds to 'if solution_plan:'
                    logger.warning(f"No solution plan generated for task {task_id}.")
                    # If no plan, task cannot be completed. Consider marking Blocked or Manual Review?
                    # For now, it will just log and move to the next task.
                    # A better approach might be to update the task status to 'Manual Review' here.
                    logger.info(f"Task {task_id} requires manual review due to failed plan generation.")
                    # Optionally update status to 'Manual Review' here if desired.


            else: # This 'else' corresponds to 'if next_task:'
                logger.info('No tasks available in Not Started status. Exiting autonomous loop.')
                break # This break exits the while True loop

            # Add a log to indicate the end of a successful or failed iteration before checking for the next task
            logger.info('Simulated iteration successful. Ready for next task.')

        # Log loop termination after the while loop exits
        logger.info('Autonomous loop terminated.')


    def _read_file_for_context(self, relative_file_path: str) -> str:
        """
        Reads content from a file, handling errors and size limits.

        Args:
            relative_file_path: The path to the file, relative to the context's base_path.

        Returns:
            The content of the file as a string, or an empty string if reading fails
            or the file exceeds the size limit.
        """
        if not isinstance(relative_file_path, str) or relative_file_path == "":
            logger.warning(f"Attempted to read file with invalid path: {relative_file_path}")
            return ""

        full_path = self.context.get_full_path(relative_file_path)

        if full_path is None:
            logger.error(f"Failed to resolve path for reading: {relative_file_path}")
            return "" # Return empty string on path resolution failure

        if not os.path.exists(full_path):
            logger.warning(f"File not found for reading: {relative_file_path}")
            return "" # Return empty string if file doesn't exist

        if not os.path.isfile(full_path):
            logger.warning(f"Path is not a file: {relative_file_path}")
            return "" # Return empty string if path is not a file

        try:
            file_size = os.path.getsize(full_path)
            if file_size > MAX_READ_FILE_SIZE:
                logger.warning(f"File exceeds maximum read size ({MAX_READ_FILE_SIZE} bytes): {relative_file_path} ({file_size} bytes)")
                return "" # Return empty string if file is too large

        except Exception as e:
            logger.error(f"Error checking file size for {relative_file_path}: {e}", exc_info=True)
            return "" # Return empty string on size check error


        try:
            with builtins.open(full_path, 'r', encoding='utf-8', errors='ignore') as f: # Use builtins.open
                content = f.read()
            logger.debug(f"Successfully read {len(content)} characters from {relative_file_path}")
            return content
        except PermissionError:
            logger.error(f"Permission denied when reading file: {relative_file_path}")
            return "" # Return empty string on permission error
        except Exception as e:
            logger.error(f"Unexpected error reading file {relative_file_path}: {e}", exc_info=True)
            return "" # Return empty string on other read errors


    def generate_solution_plan(self, task: dict) -> list[str]:
        """
        Generates a step-by-step solution plan for a given task using the LLM.

        Args:
            task: The task dictionary for which to generate a plan. Must contain
                  'task_name' and 'description'.

        Returns:
            A list of strings representing the plan steps, or an empty list if
            plan generation fails or returns an empty response.
        """
        if not isinstance(task, dict) or 'task_name' not in task or 'description' not in task:
            logger.error("Invalid task dictionary provided for plan generation.")
            return []

        task_name = task['task_name']
        description = task['description']

        # --- ADDED CONTEXT ABOUT THE TARGET FILE (Corrected Logic) ---
        target_file_context = ""
        task_target_file = task.get('target_file')

        # Corrected Logic: Always include target_file context if present
        if task_target_file:
            target_file_context = f"The primary file being modified for this task is specified as `{task_target_file}` in the task metadata. Focus your plan steps on actions related to this file.\n\n" # Added newline for formatting
        # Removed the 'elif' condition that checked for specific keywords

        # --- END ADDED CONTEXT ---


        planning_prompt = f"""You are an AI assistant specializing in software development workflows.
Your task is to generate a step-by-step solution plan for the following development task from the Metamorphic Software Genesis Ecosystem roadmap.

Task Name: {task_name}

Task Description:
{description}

{target_file_context}Please provide the plan as a numbered markdown list. Do not include any introductory or concluding remarks outside the list.
When generating steps that involve modifying the primary file for this task, ensure you refer to the file identified in the context (e.g., src/core/automation/workflow_driver.py).
"""


        # The last sentence is kept to guide the LLM's natural language, but the Driver now relies on the target_file field.

        logger.debug(f"Sending planning prompt to LLM for task '{task_name}'.")

        llm_response = self._invoke_coder_llm(planning_prompt)

        if not llm_response:
            logger.warning(f"LLM returned empty response for plan generation for task '{task_name}'.")
            return []

        plan_steps = []
        step_pattern = re.compile(r'^\s*\d+\.\s*(.*)$', re.MULTILINE)

        current_step_text = None

        for line in llm_response.splitlines():
            match = step_pattern.match(line)
            if match:
                if current_step_text is not None:
                    plan_steps.append(current_step_text.strip())
                current_step_text = match.group(1).strip()
            elif current_step_text is not None:
                current_step_text += " " + line.strip()

        if current_step_text is not None:
            plan_steps.append(current_step_text.strip())

        sanitized_steps = [re.sub(r'[*_`]', '', step).strip() for step in plan_steps]
        sanitized_steps = [step for step in sanitized_steps if step]

        logger.debug(f"Parsed and sanitized plan steps: {sanitized_steps}")

        return sanitized_steps

    def _invoke_coder_llm(self, coder_llm_prompt: str) -> str:
        """
        Invokes the Coder LLM (LLMOrchestrator) to generate code or text.

        Args:
            coder_llm_prompt: The prompt to send to the Coder LLM.

        Returns:
            Return the generated text from the LLM, or None if there was an error.
        """
        try:
            # The prompt is now constructed by the caller (autonomous_loop)
            # This method just passes it to the LLM Orchestrator.
            response = self.llm_orchestrator.generate(coder_llm_prompt)

            if response is None:
                logger.error("LLM Orchestrator generate method returned None.")
                return None

            # The stripping logic remains, as the LLM might still return markdown fences
            cleaned_response = response.strip()
            # Remove leading ```python or ``` followed by optional newline
            if cleaned_response.startswith("```python"):
                cleaned_response = cleaned_response[len("```python"):].lstrip()
            elif cleaned_response.startswith("```"):
                cleaned_response = cleaned_response[len("```"):].lstrip()

            # Remove trailing ``` followed by optional newline and whitespace
            if cleaned_response.endswith("```"):
                cleaned_response = cleaned_response[:-len("```")].rstrip()

            return cleaned_response.strip()

        except Exception as e:
            logger.error(f"Error invoking Coder LLM: {e}", exc_info=True)
            return None

    def select_next_task(self, tasks: list) -> dict | None:
        """
        Selects the next task with status 'Not Started' from the list,
        respecting 'depends_on' dependencies.

        Args:
            tasks: A list of task dictionaries. Each task must contain 'task_id',
                   'status', and optionally 'depends_on'.

        Returns:
            The first task dictionary with a status of 'Not Started' whose
            dependencies are all 'Completed', or None if no such task exists.
        """
        if not isinstance(tasks, list):
            logger.warning(f"select_next_task received non-list input: {type(tasks)}")
            return None

        # Create a quick lookup for task statuses by ID
        task_status_map = {
            task.get('task_id'): task.get('status')
            for task in tasks if isinstance(task, dict) and 'task_id' in task and 'status' in task
        }

        for task in tasks:
            if not isinstance(task, dict) or 'task_id' not in task or 'status' not in task or 'description' not in task or 'priority' not in task:
                logger.warning(f"Skipping invalid task format in list: {task}")
                continue

            task_id = task.get('task_id')
            if not self._is_valid_task_id(task_id):
                logger.warning(f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue

            if task['status'] == 'Not Started':
                depends_on = task.get('depends_on', [])

                # Validate 'depends_on' field format
                if not isinstance(depends_on, list):
                    logger.warning(f"Skipping task {task_id}: 'depends_on' field is not a list.")
                    continue

                # Check if all dependencies are 'Completed'
                all_dependencies_completed = True
                for dep_task_id in depends_on:
                    # Validate dependency task ID format
                    if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                        logger.warning(f"Skipping task {task_id}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                        all_dependencies_completed = False
                        break # Stop checking dependencies for this task

                    dep_status = task_status_map.get(dep_task_id)

                    if dep_status is None:
                        # Dependency task not found in the roadmap
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' not found in roadmap.")
                        all_dependencies_completed = False
                        break
                    elif dep_status != 'Completed':
                        # Dependency is not completed (Not Started, In Progress, Blocked)
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' status is '{dep_status}' (requires 'Completed').")
                        all_dependencies_completed = False
                        break

                if all_dependencies_completed:
                    # Found a selectable task
                    return task
            # If status is not 'Not Started', or if dependencies are not met, continue to the next task

        # No selectable task found
        return None


    def generate_coder_llm_prompts(self, task, solution_plan):
        # This method is currently not used in the autonomous_loop for generating code prompts.
        # The code prompts are constructed directly within the loop.
        # Keep this method for potential future use or refactoring.
        if not isinstance(task, dict):
            raise TypeError("Input 'task' must be a dictionary")
        if not isinstance(solution_plan, list):
            raise TypeError("Input 'solution_plan' must be a list of strings")
        if not all(isinstance(step, str) for step in solution_plan):
            raise TypeError("Input 'solution_plan' must be a list of strings")
        if 'task_name' not in task or 'description' not in task:
            raise ValueError("Task dictionary must contain 'task_name' and 'description' keys")

        task_name = task['task_name']
        description = task['description']
        user_actionable_steps_md = self.generate_user_actionable_steps(solution_plan)

        prompt = f"""You are a Coder LLM expert in Python, asked to implement code for the following task:
Task Name: {task_name}

Task Description:
{description}

Implement the following steps:
{user_actionable_steps_md}

Requirements:

Follow best practices for code quality and style.
Prioritize security, and prevent code injection vulnerabilities.
"""
        return [prompt]


    def generate_user_actionable_steps(self, steps):
        if not isinstance(steps, list):
            raise TypeError("generate_user_actionable_steps expects a list of strings")
        if not all(isinstance(step, str) for step in steps):
            raise TypeError("generate_user_actionable_steps expects a list of strings")

        if not steps:
            return ""

        markdown_steps = ""
        for i, step in enumerate(steps):
            # FIX: Apply html.escape here if this output is intended for HTML rendering
            # For now, matching the test expectation of no escaping in the code
            # Apply html.escape to the step description
            escaped_step = html.escape(step)
            markdown_steps += f"{i + 1}. - [ ] {escaped_step}\n" # Changed from 1.  - to 1. -
        return markdown_steps

    def load_roadmap(self, roadmap_file_path):
        tasks = []
        max_file_size = 20000
        if roadmap_file_path is None: # Handle None roadmap_file_path explicitly
            logger.error(f"Failed to load roadmap from None: roadmap_file_path is None")
            return tasks
        # Use the provided roadmap_file_path directly, assuming it's already resolved or validated by the caller (API endpoint)
        # If loading from within the loop, start_workflow ensures it's a full path via context.get_full_path
        full_roadmap_path = roadmap_file_path # Use the path as provided

        if not os.path.exists(full_roadmap_path):
            logger.error(f"ROADMAP.json file not found at path: {full_roadmap_path}")
            return tasks

        if os.path.getsize(full_roadmap_path) > max_file_size:
            logger.error(
                f"ROADMAP.json file exceeds maximum allowed size of {max_file_size} bytes.")
            return tasks

        try:
            with builtins.open(full_roadmap_path, 'r') as f: # Use builtins.open
                roadmap_data = json.load(f)
        except json.JSONDecodeError:
            logger.error(f"Invalid JSON in roadmap file: {full_roadmap_path}")
            return tasks

        if 'tasks' not in roadmap_data:
            logger.error("ROADMAP.json must contain a 'tasks' key.")
            return tasks

        if not isinstance(roadmap_data['tasks'], list):
            logger.error("'tasks' must be a list in ROADMAP.json.")
            return tasks

        for task_data in roadmap_data['tasks']:
            if not isinstance(task_data, dict):
                logger.warning(f"Skipping invalid task (not a dictionary): {task_data}")
                continue

            required_keys = ['task_id', 'priority', 'task_name', 'status', 'description']
            if not all(key in task_data for key in required_keys):
                logger.warning(f"Task missing required keys: {task_data}. Required keys are: {required_keys}")
                continue

            task_id = task_data['task_id']
            if not self._is_valid_task_id(task_id):
                logger.warning(
                    f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue

            task_name = task_data['task_name']
            if len(task_name) > 150:
                logger.warning(f"Task Name '{task_name}' exceeds 150 characters. Task will be skipped.")
                continue

            task_description = task_data['description']
            # Escape HTML characters in the description to prevent XSS in logs/prompts
            escaped_description = html.escape(task_description)

            # --- ADDED: Load and validate 'depends_on' field ---
            depends_on = task_data.get('depends_on', [])
            if not isinstance(depends_on, list):
                logger.warning(f"Skipping task {task_id}: 'depends_on' field is not a list.")
                continue # Skip task if depends_on is not a list

            is_depends_on_valid = True
            validated_depends_on = []
            for dep_task_id in depends_on:
                if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                    logger.warning(f"Skipping task {task_id}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                    is_depends_on_valid = False
                    break # Stop processing depends_on for this task if any invalid ID is found
                validated_depends_on.append(dep_task_id)

            if not is_depends_on_valid:
                continue # Skip the task if any dependency ID was invalid
            # --- END ADDED ---


            task = {
                'task_id': task_id,
                'priority': task_data['priority'],
                'task_name': task_name,
                'status': task_data['status'],
                'description': escaped_description,
                'target_file': task_data.get('target_file'),
                'depends_on': validated_depends_on # ADDED: Store the validated depends_on list
            }
            tasks.append(task)
        return tasks

    def _is_valid_task_id(self, task_id):
        """Validates task_id to ensure it only contains allowed characters and format."""
        if not isinstance(task_id, str):
            return False
        # Allow alphanumeric, underscores, and hyphens, must start with alphanumeric
        # Disallow dots (.) in task IDs as they are used in file paths and could be confusing/risky
        # Updated regex to allow hyphens and underscores at the end
        # FIX: Corrected regex to allow hyphens and underscores *within* the ID, not just at the end
        return bool(re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9_-]*$', task_id))


    def file_exists(self, relative_file_path):
        """Checks if a file exists in the workspace using the context's base path."""
        if not isinstance(relative_file_path, str):
            logger.warning(f"file_exists received non-string input: {type(relative_file_path)}")
            return False
        try:
            # Resolve the path relative to the base_path first, then resolve the full path
            full_path = self.context.get_full_path(relative_file_path)
            if full_path is None: # Check if context path resolution failed
                logger.warning(f"Failed to resolve path for existence check: {relative_file_path}")
                return False
            # No need to call resolve() again here, get_full_path already returns a resolved path
            resolved_path = Path(full_path)
        except Exception as e:
            logger.error(f"Error resolving filepath {relative_file_path} for existence check: {e}",
                         exc_info=True)
            return False

        # The primary check is whether the resolved path actually exists and is a file.
        return os.path.exists(resolved_path) and os.path.isfile(resolved_path)

    def list_files(self):
        """Lists files and directories in the workspace root."""
        base_path = self.context.base_path
        entries = []
        try:
            # Use the resolved base path from the context
            resolved_base_path_str = self.context.get_full_path("") # Resolve empty string to get base path
            if resolved_base_path_str is None:
                logger.error(f"Failed to resolve base path for listing: {base_path}")
                return []
            resolved_base_path = Path(resolved_base_path_str)

            if not resolved_base_path.is_dir():
                logger.error(f"Base path is not a valid directory: {base_path}")
                return []

            # Use resolved_base_path for listing
            for name in os.listdir(resolved_base_path):
                # Add check using _is_valid_filename # ADDED
                if not self._is_valid_filename(name):
                    logger.warning(f"Skipping listing of potentially unsafe filename: {name}")
                    continue
                # END ADDED

                full_path = resolved_base_path / name # Use Path object for joining

                if full_path.is_file(): # Use Path object methods
                    entries.append({'name': name, 'status': 'file'})
                elif full_path.is_dir(): # Use Path object methods
                    entries.append({'name': name, 'status': 'directory'})
        except Exception as e:
            logger.error(f"Error listing files in {base_path}: {e}", exc_info=True)
            return []
        return entries

    def _is_valid_filename(self, filename):
        """Basic validation for filenames to prevent listing malicious names."""
        if not isinstance(filename, str):
            return False
        # Disallow path traversal sequences and directory separators
        # This check is redundant if using Path.resolve() correctly, but adds a layer.
        if '..' in filename or '/' in filename or '\\' in filename: # Corrected backslash escape
            return False
        # Ensure it's not just a dot or dot-dot
        if filename in ['.', '..']:
            return False
        # Allow alphanumeric, underscores, hyphens, and dots. Must start with alphanumeric.
        # Disallow trailing dot.
        # CORRECTED REGEX and added explicit check for trailing dot
        # FIX: Corrected regex to allow dots *within* the filename, not just at the end
        if not re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9._-]*$', filename):
            return False
        if filename.endswith('.'): # Explicitly disallow trailing dot
            return False
        return True

    def _write_output_file(self, filepath, content, overwrite=False):
        """
        Writes content to a file using the write_file utility function, respecting base path.

        Args:
            filepath (str): The path to the file, relative to the context's base_path.
            content (str): The content to write.
            overwrite (bool): Whether to overwrite existing files. Defaults to False.

        Returns:
            bool: True if file writing was successful, False otherwise.

        Raises:
            FileExistsError: If overwrite is False and the file already exists.
        """
        if not isinstance(filepath, str) or filepath == "":
            logger.error(f"_write_output_file received invalid filepath: {filepath}")
            return False
        try:
            # Resolve the path relative to the base_path first, then resolve the full path
            full_path = self.context.get_full_path(filepath)
            if full_path is None: # Check if context path resolution failed
                logger.error(f"Failed to resolve path for writing: {filepath}")
                return False
            # No need to call resolve() again here, get_full_path already returns a resolved path
            resolved_filepath = Path(full_path)
        except Exception as e:
            logger.error(f"Error resolving filepath {filepath} for writing: {e}", exc_info=True)
            return False

        # Ensure the directory exists before writing
        parent_dir = resolved_filepath.parent
        if not parent_dir.exists():
            try:
                parent_dir.mkdir(parents=True, exist_ok=True)
                logger.info(f"Created directory: {parent_dir}")
            except Exception as e:
                logger.error(f"Failed to create directory {parent_dir}: {e}", exc_info=True)
                return False

        try:
            # Pass the resolved full path to write_file
            result = write_file(str(resolved_filepath), content, overwrite=overwrite)
            # write_file already logs success/failure internally
            return result
        except FileExistsError as e:
            # Re-raise FileExistsError as it's expected to be caught by the caller
            raise e
        except FileNotFoundError as e:
            logger.error(f"File not found error when writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False
        except PermissionError as e:
            logger.error(f"Permission error when writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False
        except Exception as e:
            logger.error(f"Unexpected error writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False # ADDED: Return False on generic exception

    def execute_tests(self, test_command: list[str], cwd: str) -> tuple[int, str, str]:
        stdout = ""
        stderr = ""
        return_code = 1

        logger.info(f"Executing command: {' '.join(test_command)} in directory: {cwd or 'current directory'}")

        try:
            process = subprocess.run(
                test_command,
                cwd=cwd,
                capture_output=True,
                text=True,
                check=False
            )

            stdout = process.stdout
            stderr = process.stderr
            return_code = process.returncode

            if return_code == 0:
                logger.info(f"Command executed successfully. Return code: {return_code}")
            else:
                logger.error(f"Command failed with return code: {return_code}")

            logger.debug(f"STDOUT:\n{stdout}")
            logger.debug(f"STDERR:\n{stderr}")

        except FileNotFoundError:
            error_msg = f"Error: Command executable not found. Ensure '{test_command[0]}' is in your system's PATH."
            stderr = error_msg
            return_code = 127
            logger.error(error_msg)

        except Exception as e:
            error_msg = f"An unexpected error occurred during command execution: {e}"
            stderr = error_msg
            return_code = 1
            logger.error(error_msg)

        # Store stdout/stderr for potential use in remediation
        self._current_task_results['test_stdout'] = stdout
        self._current_task_results['test_stderr'] = stderr
        # --- ADDED: Store test command and cwd for potential re-execution ---
        self._current_task_results['last_test_command'] = test_command
        self._current_task_results['last_test_cwd'] = cwd
        # --- END ADDED ---
        return return_code, stdout, stderr

    def _merge_snippet(self, existing_content: str, snippet: str) -> str:
        """
        Merges a generated code snippet into existing file content.

        If the METAMORPHIC_INSERT_POINT marker is found, the snippet is inserted
        at the first occurrence of the marker. Otherwise, the snippet is appended
        to the existing content with a newline separator.

        Args:
            existing_content: The current content of the file.
            snippet: The code snippet generated by the Coder LLM.

        Returns:
            The merged content as a string.
        """
        if not snippet:
            return existing_content # Return existing content if snippet is empty

        marker_index = existing_content.find(METAMORPHIC_INSERT_POINT)

        if marker_index != -1:
            # Marker found, insert snippet at the marker position
            before_marker = existing_content[:marker_index]
            after_marker = existing_content[marker_index + len(METAMORPHIC_INSERT_POINT):]
            # Insert the snippet between the parts, replacing the marker
            return before_marker + snippet + after_marker
        else:
            # Marker not found, append snippet with a newline separator
            if not existing_content:
                return snippet # If existing is empty, just return snippet
            # Ensure a newline before appending if existing content doesn't end with one
            # FIX: Removed .strip() from endswith check
            if existing_content and not existing_content.endswith('\n'):
                return existing_content + "\n" + snippet
            # If existing content ends with a newline, just append the snippet
            return existing_content + snippet

    def _parse_test_results(self, raw_output: str) -> dict:
        """
        Parses raw pytest output to extract test results.

        Args:
            raw_output: The raw string output from a pytest subprocess run.

        Returns:
            A dictionary containing parsed test results:
            {'passed': int, 'failed': int, 'total': int, 'status': str, 'message': str}
            Status is 'passed', 'failed', or 'error'.
        """
        if not raw_output:
            logger.warning("Received empty output for test results parsing.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Received empty output.'}

        # Regex to find the final summary line(s)
        # Look for lines starting with '==' and containing 'test session' or test counts
        summary_lines = [line for line in raw_output.splitlines() if line.strip().startswith('==') and ('test session' in line or 'passed' in line or 'failed' in line or 'skipped' in line or 'error' in line)]

        if not summary_lines:
            logger.warning("Could not find pytest summary lines in output.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not find pytest summary lines in output.'}

        # Focus on the last summary line, which usually contains the final counts
        final_summary_line = summary_lines[-1]

        # Regex to extract counts (passed, failed, skipped, error)
        counts_pattern = re.compile(r'(\d+) (passed|failed|skipped|error)')
        matches = counts_pattern.findall(final_summary_line)

        passed = 0
        failed = 0
        skipped = 0
        errors = 0

        for count_str, status_str in matches:
            try:
                count = int(count_str)
                if status_str == 'passed':
                    passed = count
                elif status_str == 'failed':
                    failed = count
                elif status_str == 'skipped':
                    skipped = count
                elif status_str == 'error':
                    errors = count
            except ValueError:
                logger.warning(f"Could not parse count '{count_str}' from summary line: {final_summary_line}")
                # Continue parsing other matches

        total = passed + failed + skipped + errors

        if total == 0 and (passed > 0 or failed > 0 or skipped > 0 or errors > 0):
            logger.warning(f"Parsed counts ({passed}p, {failed}f, {skipped}s, {errors}e) but total is 0. Summary line: {final_summary_line}")
            total = passed + failed + skipped + errors


        status = 'passed' if failed == 0 and errors == 0 and total > 0 else 'failed'
        if total == 0:
            status = 'error' # If no tests ran, consider it an error state for parsing

        if total == 0 and not matches:
            logger.warning(f"Could not parse any counts from summary line: {final_summary_line}")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not parse test results output.'}


        results = {
            'passed': passed,
            'failed': failed,
            'total': total,
            'status': status,
            'message': 'Parsed successfully.' if status != 'error' else 'Could not parse test results output.'
        }

        logger.debug(f"Parsed test results: {results}")
        return results

    # ADDED: Implementation of generate_grade_report and _calculate_grades
    def generate_grade_report(self, task_id: str, validation_results: dict) -> str:
        """
        Generates a structured JSON Grade Report based on validation results.

        Args:
            task_id: The ID of the task being reported on.
            validation_results: A dictionary containing results from automated validation steps.
                                Expected keys: 'test_results', 'code_review_results',
                                'ethical_analysis_results'. (Security results are within code_review_results)

        Returns:
            A JSON string representing the Grade Report.
        """
        report = {
            "task_id": task_id,
            "timestamp": datetime.utcnow().isoformat(),
            "validation_results": {
                "tests": validation_results.get('test_results', {}),
                "code_review": validation_results.get('code_review_results', {}), # Includes static analysis and bandit
                "ethical_analysis": validation_results.get('ethical_analysis_results', {})
            },
            "grades": self._calculate_grades(validation_results)
        }

        # Use standard json.dumps for now
        return json.dumps(report, indent=2)

    def _calculate_grades(self, validation_results: dict) -> dict:
        """
        Calculates probability-based grades based on validation results.

        Weights:
            - Probability of Non-Regression: 20%
            - Probability of Test Success: 30%
            - Code Style Compliance Probability: 10%
            - Probability of Ethical Policy Compliance Probability: 20%
            - Probability of Security Soundness: 20%

        Args:
            validation_results: Dictionary of validation results.

        Returns:
            A dictionary with dimension-specific grades and an overall grade.
        """
        grades = {
            "non_regression": {"percentage": 0, "justification": "No non-regression tests executed."}, # Placeholder
            "test_success": {"percentage": 0, "justification": "No test results available."},
            "code_style": {"percentage": 0, "justification": "No code review results available."},
            "ethical_policy": {"percentage": 0, "justification": "No ethical analysis results available."},
            "security_soundness": {"percentage": 0, "justification": "No security results available."}
        }

        # Calculate Test Success Grade (30%)
        test_results = validation_results.get('test_results')
        if test_results and test_results.get('status') != 'error' and test_results.get('total', 0) > 0:
            percentage = 100 * (test_results.get('passed', 0) / test_results.get('total')) # Partial credit based on pass rate
            grades['test_success'] = {
                "percentage": round(percentage),
                "justification": f"Tests executed: {test_results.get('total')}, Passed: {test_results.get('passed')}, Failed: {test_results.get('failed')}, Status: {test_results.get('status')}"
            }
        elif test_results and test_results.get('status') == 'error':
            grades['test_success'] = {
                "percentage": 0,
                "justification": f"Test execution or parsing error: {test_results.get('message')}"
            }


        # Calculate Code Style Grade (10%) and Security Soundness Grade (20%)
        code_review_results = validation_results.get('code_review_results')
        if code_review_results and code_review_results.get('status') != 'error':
            all_findings = code_review_results.get('static_analysis', [])

            # Separate findings into Code Style and Security based on severity prefix
            code_style_findings = [f for f in all_findings if not f.get('severity', '').startswith('security')]
            security_findings = [f for f in all_findings if f.get('severity', '').startswith('security')]

            # --- Code Style Grade Calculation ---
            # Count high severity style findings (errors, warnings, style, info) - adjust based on desired strictness
            # Let's consider 'error' and 'warning' from Flake8 as style issues for this grade
            high_style_issues = [f for f in code_style_findings if f.get('severity') in ['error', 'warning']]
            other_style_issues = [f for f in code_style_findings if f.get('severity') not in ['error', 'warning']]

            style_high_penalty = 15 # Each high style issue reduces score by 15%
            style_other_penalty = 3 # Each other style issue reduces score by 3%

            calculated_style_percentage = 100 - (len(high_style_issues) * style_high_penalty + len(other_style_issues) * style_other_penalty)
            style_percentage = max(0, calculated_style_percentage) # Cap at 0%

            grades['code_style'] = {
                "percentage": style_percentage,
                "justification": f"Code review found {len(code_style_findings)} style issues ({len(high_style_issues)} high severity style). Status: {code_review_results.get('status')}"
            }

            # --- Security Soundness Grade Calculation ---
            high_security_findings = [f for f in security_findings if f.get('severity') == 'security_high']
            medium_security_findings = [f for f in security_findings if f.get('severity') == 'security_medium']
            low_security_findings = [f for f in security_findings if f.get('severity') == 'security_low']

            # Arbitrary penalty factors for security findings
            high_sec_penalty = 50 # Each high security issue reduces score by 50%
            medium_sec_penalty = 10 # Each medium security issue reduces score by 10%
            low_sec_penalty = 2 # Each low security issue reduces score by 2%

            calculated_security_percentage = 100 - (len(high_security_findings) * high_sec_penalty +
                                                    len(medium_security_findings) * medium_sec_penalty +
                                                    len(low_security_findings) * low_sec_penalty)
            security_percentage = max(0, calculated_security_percentage) # Cap at 0%

            grades['security_soundness'] = {
                "percentage": security_percentage,
                "justification": f"Security scan found {len(security_findings)} security findings ({len(high_security_findings)} high, {len(medium_security_findings)} medium, {len(low_security_findings)} low)."
            }

        elif code_review_results and code_review_results.get('status') == 'error':
            error_justification = f"Code review/security execution error: {code_review_results.get('errors', {}).get('flake8', 'N/A')}, {code_review_results.get('errors', {}).get('bandit', 'N/A')}"
            grades['code_style'] = {
                "percentage": 0,
                "justification": error_justification
            }
            grades['security_soundness'] = {
                "percentage": 0,
                "justification": error_justification
            }


        # Calculate Ethical Policy Grade (20%)
        # FIX: Correct the key lookup from 'ethical_analysis' to 'ethical_analysis_results'
        ethical_results = validation_results.get('ethical_analysis_results') # CORRECTED KEY
        if ethical_results and ethical_results.get('overall_status') != 'error':
            percentage = 100 if ethical_results.get('overall_status') == 'approved' else 0
            justification = f"Ethical analysis status: {ethical_results.get('overall_status')}. Policy: {ethical_results.get('policy_name', 'N/A')}"
            if ethical_results.get('overall_status') == 'rejected':
                violations = [k for k, v in ethical_results.items() if isinstance(v, dict) and v.get('status') == 'violation']
                justification += f". Violations: {', '.join(violations)}"
            elif ethical_results.get('overall_status') == 'skipped':
                percentage = 0 # Skipped is treated as 0 for grading
                justification = f"Ethical analysis skipped: {ethical_results.get('message', 'Unknown reason')}"

            # FIX: Add the missing assignment here - THIS WAS ALREADY PRESENT, NO CHANGE NEEDED HERE
            grades['ethical_policy'] = {
                "percentage": percentage,
                "justification": justification
            }
        elif ethical_results and ethical_results.get('overall_status') == 'error':
            grades['ethical_policy'] = {
                "percentage": 0,
                "justification": f"Ethical analysis execution error: {ethical_results.get('message', 'Unknown error')}"
            }


        # Calculate Non-Regression Grade (20%) - Placeholder for now
        # This requires comparing current state/behavior to previous, which is complex.
        # For 1.6f, this will be a placeholder.
        # Simple heuristic: 100% if Test Success is 100%, 0% otherwise.
        grades['non_regression'] = {
            "percentage": 100 if grades['test_success']['percentage'] == 100 else 0,
            "justification": "Non-regression testing is a placeholder. Graded based on Test Success (100% if tests passed, 100% if no tests ran, 0% otherwise)." # Updated justification
        }


        # Calculate Overall Percentage Grade
        # Weights: Non-Regression (20%), Test Success (30%), Code Style (10%), Ethical Policy (20%), Security Soundness (20%)
        overall_percentage = (
            grades['non_regression']['percentage'] * 0.20 +
            grades['test_success']['percentage'] * 0.30 +
            grades['code_style']['percentage'] * 0.10 +
            grades['ethical_policy']['percentage'] * 0.20 +
            grades['security_soundness']['percentage'] * 0.20
        )

        grades['overall_percentage_grade'] = round(overall_percentage)

        return grades

    def _parse_and_evaluate_grade_report(self, grade_report_json: str) -> dict:
        """
        Parses a JSON Grade Report, evaluates results, and determines the recommended next action.

        Args:
            grade_report_json: The JSON string representing the Grade Report.

        Returns:
            A dictionary containing the recommended_action and justification.
        """
        logger.info("Parsing and evaluating Grade Report...")
        try:
            report_data = json.loads(grade_report_json)
        except json.JSONDecodeError as e:
            logger.error(f"Failed to parse Grade Report JSON: {e}", exc_info=True)
            return {
                "recommended_action": "Manual Review Required",
                "justification": f"Failed to parse Grade Report JSON: {e}"
            }

        # Extract key metrics, handling missing keys
        grades = report_data.get('grades', {})
        validation_results = report_data.get('validation_results', {})

        overall_percentage_grade = grades.get('overall_percentage_grade', 0)
        test_results = validation_results.get('tests', {})
        code_review_results = validation_results.get('code_review', {})
        ethical_analysis_results = validation_results.get('ethical_analysis', {})

        logger.info(f"Grade Report Metrics: Overall Grade={overall_percentage_grade}%, Test Status={test_results.get('status')}, Ethical Status={ethical_analysis_results.get('overall_status')}, Code Review Status={code_review_results.get('status')}")

        recommended_action = "Manual Review Required"
        justification = "Default action based on unhandled scenario."

        # Rule 1: Perfect Score
        if overall_percentage_grade == 100:
            recommended_action = "Completed"
            justification = "Overall grade is 100%."
        # Rule 2: Critical Ethical Violation
        elif ethical_analysis_results.get('overall_status') == 'rejected':
            recommended_action = "Blocked"
            justification = "Ethical analysis rejected the code."
        # Rule 3: High-Risk Security Finding
        elif code_review_results.get('static_analysis') and any(f.get('severity') == 'security_high' for f in code_review_results['static_analysis']):
            recommended_action = "Blocked"
            justification = "High-risk security findings detected."
        # Rule 4: Test Failures
        elif test_results.get('status') == 'failed':
            recommended_action = "Regenerate Code"
            justification = "Automated tests failed."
        # Rule 5: Below Perfect but Acceptable for Regeneration
        elif overall_percentage_grade >= 80: # Threshold for regeneration
            recommended_action = "Regenerate Code"
            justification = f"Overall grade ({overall_percentage_grade}%) is below 100% but meets regeneration threshold."
        # Default: Manual Review Required
        else:
            recommended_action = "Manual Review Required"
            justification = f"Overall grade ({overall_percentage_grade}%) is below regeneration threshold or other issues require manual review."

        logger.info(f"Recommended Action: {recommended_action}. Justification: {justification}")

        return {
            "recommended_action": recommended_action,
            "justification": justification
        }

    def _safe_write_roadmap_json(self, roadmap_path: str, new_content: dict) -> bool:
        """
        Safely writes updated content to the ROADMAP.json file using an atomic write pattern.

        Args:
            roadmap_path: The relative path to the roadmap file (e.g., "ROADMAP.json").
            new_content: The new content for the roadmap file as a dictionary.

        Returns:
            True if the write was successful, False otherwise.
        """
        # 1. Resolve the full path safely
        resolved_filepath = self.context.get_full_path(roadmap_path)
        if resolved_filepath is None:
            logger.error(f"Security alert: Path traversal attempt detected for roadmap file: {roadmap_path}")
            return False

        # 2. Validate content structure
        if not isinstance(new_content, dict):
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Content is not a dictionary.")
            return False
        if 'tasks' not in new_content:
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Missing 'tasks' key.")
            return False

        # 3. Implement atomic write
        resolved_filepath_obj = Path(resolved_filepath)
        roadmap_dir = resolved_filepath_obj.parent
        temp_filename = f".{resolved_filepath_obj.name}.{uuid.uuid4()}.tmp"
        temp_filepath = roadmap_dir / temp_filename

        # Clean up potential leftover temporary file from a previous failed attempt
        if temp_filepath.exists():
            try:
                os.remove(temp_filepath)
                logger.debug(f"Cleaned up leftover temporary file: {temp_filepath}")
            except Exception as cleanup_e:
                logger.warning(f"Failed to clean up leftover temporary file {temp_filepath}: {cleanup_e}")


        try:
            # Write to temporary file
            with builtins.open(temp_filepath, 'w', encoding='utf-8') as f: # Use builtins.open
                json.dump(new_content, f, indent=2)

            # Atomically replace the original file
            os.replace(temp_filepath, resolved_filepath)

            logger.info(f"Successfully wrote updated roadmap to {roadmap_path}")
            return True

        except (IOError, OSError, PermissionError, json.JSONDecodeError) as e:
            logger.error(f"Error writing roadmap file {roadmap_path}: {e}", exc_info=True)
            # Clean up temporary file in case of failure after temp file is created but before replace
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after error: {cleanup_e}")
                except Exception as cleanup_e:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after error: {cleanup_e}")
            return False
        except Exception as cleanup_e: # Corrected indentation for this except block
            logger.error(f"Unexpected error during roadmap file write {roadmap_path}: {cleanup_e}", exc_info=True)
            # Clean up temporary file in case of unexpected failure
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after unexpected error: {cleanup_e}")
                except Exception as cleanup_e:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after unexpected error: {cleanup_e}")
            return False

    def _identify_remediation_target(self, grade_report_json: str) -> str | None:
        """
        Parses the grade report JSON to identify the primary target for remediation.

        Args:
            grade_report_json: The JSON string of the grade report.

        Returns:
            "Code Style", "Ethical Transparency", or None if no clear target identified.
        """
        try:
            report_data = json.loads(grade_report_json)
            grades = report_data.get('grades', {})
            validation = report_data.get('validation_results', {})

            # Prioritize critical failures first (though remediation might not apply)
            if validation.get('ethical_analysis', {}).get('overall_status') == 'rejected':
                if validation.get('ethical_analysis', {}).get('TransparencyScore', {}).get('status') == 'violation':
                    logger.debug("Identified Ethical Transparency as remediation target.")
                    return "Ethical Transparency"
                else:
                    logger.debug("Ethical rejection not due to TransparencyScore, no specific remediation target.")
                    # Continue to check code style remediation possibility

            # Check for Code Style issues if no specific ethical transparency issue was found
            code_style_grade = grades.get('code_style', {}).get('percentage', 100)
            if code_style_grade < 100: # Assuming 100 means no style issues
                if validation.get('code_review', {}).get('status') == 'failed':
                    logger.debug("Identified Code Style as remediation target.")
                    return "Code Style"
                else:
                    logger.debug("Code style grade below 100, but code review status not 'failed'.")
                    pass # Continue to check other targets if any

            # <--- Add check for test failures here for task 1.7.5 --->
            # Note: This method is primarily for identifying *which* remediation to attempt first
            # if multiple issues exist. The autonomous_loop already checks test status directly.
            # Adding a check here would allow prioritizing test failures if desired,
            # but for now, the loop's logic is sufficient.

            logger.debug("No specific remediation target identified from grade report.")
            return None
        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for remediation target identification.")
            return None
        except Exception as e:
            logger.error(f"Error identifying remediation target: {e}", exc_info=True)
            return None

    def _attempt_code_style_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        """
        Attempts to remediate code style issues using LLM feedback.
        (Implementation as provided in the codebase)
        """
        logger.info(f"Attempting code style remediation for {file_path}...")
        try:
            report_data = json.loads(grade_report_json)
            code_review_results = report_data.get('validation_results', {}).get('code_review', {})
            findings = code_review_results.get('static_analysis', [])

            style_feedback = [
                f"- {f.get('code')} at line {f.get('line')}: {f.get('message')}"
                for f in findings if not f.get('severity', '').startswith('security')
            ]

            if not style_feedback:
                logger.warning("No specific code style feedback found to provide to LLM.")
                return False

            feedback_str = "\n".join(style_feedback)
            logger.debug(f"Extracted code style feedback:\n{feedback_str}")

            feedback_prompt = f"""You are a Coder LLM expert in Python code style (PEP 8, Flake8).
The following Python code failed automated code style checks.

File Path: {file_path}
Original Task: "{task.get('task_name', 'Unknown Task')}"
Plan Step: "{step_desc}"

Code with Issues:
```python
{original_code}
```

Identified Code Style Issues (e.g., Flake8):
{feedback_str}

Your task is to rewrite the entire code block above, fixing only the identified code style issues.

Maintain all original logic and functionality.
Adhere strictly to PEP 8 guidelines.
Ensure the corrected code passes Flake8 checks based on the feedback provided.
Output only the complete, corrected Python code. Do not include explanations or markdown fences.
"""
            logger.debug("Invoking Coder LLM for code style remediation...")
            corrected_code = self._invoke_coder_llm(feedback_prompt)


            if not corrected_code or corrected_code.strip() == original_code.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged.")
                return False

            logger.info("LLM provided corrected code. Applying and re-validating...")

            content_to_write = corrected_code
            write_success = self._write_output_file(file_path, content_to_write, overwrite=True)

            if write_success:
                try:
                    logger.info(f"Re-running code review for {file_path} after remediation...")
                    new_review_results = self.code_review_agent.analyze_python(content_to_write)
                    self._current_task_results['code_review_results'] = new_review_results
                    logger.info(f"Code Review Results after remediation: {new_review_results}")
                    if new_review_results.get('status') == 'success':
                        logger.info("Code style remediation appears successful based on re-scan.")
                    elif new_review_results.get('status') == 'failed':
                        logger.warning("Code style issues persist after remediation attempt.")
                    else:
                        logger.error("Error occurred during code review re-scan after remediation.")
                except Exception as e:
                    logger.error(f"Error occurred during code review re-scan after remediation: {e}", exc_info=True)
                    self._current_task_results['code_review_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                return True # Return True if write succeeded, even if re-validation failed
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.")
                return False # Return False if write failed
        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for code style remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during code style remediation: {e}", exc_info=True)
            return False

    def _attempt_ethical_transparency_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        """
        Attempts to remediate ethical transparency issues (missing docstrings) using LLM feedback.
        (Implementation as provided in the codebase)
        """
        logger.info(f"Attempting ethical transparency remediation for {file_path}...")
        try:
            report_data = json.loads(grade_report_json)
            ethical_results = report_data.get('validation_results', {}).get('ethical_analysis', {})
            transparency_details = ethical_results.get('TransparencyScore', {})

            if transparency_details.get('status') != 'violation':
                logger.warning("Ethical transparency remediation triggered, but no violation found in report.")
                return False

            feedback_str = transparency_details.get('details', "Missing required docstring(s).")
            logger.debug(f"Extracted ethical transparency feedback: {feedback_str}")

            feedback_prompt = f"""You are a Coder LLM expert in Python documentation and code transparency.
The following Python code failed an automated ethical transparency check, likely due to missing docstrings.

File Path: {file_path}
Original Task: "{task.get('task_name', 'Unknown Task')}"
Plan Step: "{step_desc}"

Code with Issues:
```python
{original_code}
```

Identified Transparency Issue:
{feedback_str}

Your task is to rewrite the entire code block above, adding the necessary docstrings to satisfy the transparency requirement.

Add a module-level docstring if missing.
Add docstrings to all functions and classes.
Docstrings should clearly explain the purpose, arguments, and return values (if any).
Maintain all original logic and functionality.
Output only the complete, corrected Python code with added docstrings. Do not include explanations or markdown fences.
"""
            logger.debug("Invoking Coder LLM for ethical transparency remediation...")
            corrected_code = self._invoke_coder_llm(feedback_prompt)


            if not corrected_code or corrected_code.strip() == original_code.strip():
                logger.warning("LLM did not provide corrected code or code was unchanged.")
                return False

            logger.info("LLM provided corrected code with docstrings. Applying and re-validating...")

            content_to_write = corrected_code
            write_success = self._write_output_file(file_path, content_to_write, overwrite=True)

            if write_success:
                if self.default_policy_config:
                    try:
                        logger.info(f"Re-running ethical analysis for {file_path} after remediation...")
                        new_ethical_results = self.ethical_governance_engine.enforce_policy(content_to_write, self.default_policy_config)
                        self._current_task_results['ethical_analysis_results'] = new_ethical_results
                        logger.info(f"Ethical Analysis Results after remediation: {new_ethical_results}")
                        if new_ethical_results.get('overall_status') == 'approved':
                            logger.info("Ethical transparency remediation appears successful based on re-scan.")
                        elif new_ethical_results.get('overall_status') == 'rejected':
                            logger.warning("Ethical transparency violation persists after remediation attempt.")
                        else:
                            logger.error("Error or skip occurred during ethical analysis re-scan after remediation.")
                    except Exception as e:
                        logger.error(f"Error occurred during ethical analysis re-scan after remediation: {e}", exc_info=True)
                        self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': f"Re-validation error: {e}"}
                else:
                    logger.warning("Cannot re-run ethical analysis after remediation: Default policy not loaded.")
                    self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded for re-scan.'}
                return True # Return True if write succeeded, even if re-validation failed
            else:
                logger.error(f"Failed to write corrected code to {file_path}. Aborting remediation.")
                return False # Return False if write failed
        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for ethical transparency remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during ethical transparency remediation: {e}", exc_info=True)
            return False

    def _attempt_test_failure_remediation(self, grade_report_json: str, task: dict, step_desc: str, file_path: str, original_code: str) -> bool:
        """
        Attempts to remediate test failures using LLM feedback.

        Args:
            grade_report_json: JSON string of the grade report.
            task: The current task dictionary.
            step_desc: The description of the plan step being executed (e.g., "Test Failure Remediation").
            file_path: The path to the file being modified.
            original_code: The code content before the remediation attempt.

        Returns:
            True if remediation was attempted and write succeeded, False otherwise.
        """
        logger.info(f"Attempting test failure remediation for {file_path}...")
        try:
            # No need to parse grade_report_json here, test results are in _current_task_results
            stdout = self._current_task_results.get('test_stdout', '')
            stderr = self._current_task_results.get('test_stderr', '')
            test_results = self._current_task_results.get('test_results', {})

            if test_results.get('status') != 'failed':
                logger.warning("Test failure remediation triggered, but test status is not 'failed'.")
                return False

            logger.debug(f"Test failure details - Stdout: {stdout}, Stderr: {stderr}")
            # Read current file content again, as it might have been modified by previous remediation attempts
            current_file_content = self._read_file_for_context(file_path)

            if not current_file_content or not file_path:
                logger.error(f"Failed to read current file content for {file_path} during test remediation. Cannot attempt remediation.")
                return False

            task_name = task.get('task_name', 'Unknown Task')
            task_description = task.get('description', 'No description provided')

            prompt = f"""
You are tasked with fixing the following test failure in the Python code.

Task: {task_name}
Description: {task_description}
File to modify: {file_path}
Current code content:
```python
{current_file_content}
```

Test execution output:
Stdout:
```
{stdout}
```
Stderr:
```
{stderr}
```

Instructions:

Analyze the test failure output (Stdout and Stderr) and the current code content to identify the root cause of the test failures.
Generate only the Python code snippet needed to fix the issue. This snippet should contain the necessary modifications to the code in {file_path}.
Do NOT include any surrounding text, explanations, or markdown code block fences (```). Provide just the raw code lines that need to be added or modified.
Maintain all original logic and functionality not related to the test failures.
Adhere to PEP 8 style guidelines.
Note: The Debug Agent (task_2_2_6) is NOT available; you must generate the fix directly based on the provided information.
Your response should be the corrected code snippet that addresses the test failure based on the provided context and error messages.
"""
            logger.debug("Invoking Coder LLM for test failure remediation...")
            fixed_snippet = self._invoke_coder_llm(prompt)


            if not fixed_snippet or fixed_snippet.strip() == current_file_content.strip(): # Compare against current content
                logger.warning("LLM did not provide corrected code or code was unchanged for test failure remediation.")
                return False

            logger.info("LLM provided corrected code for test failure. Applying and re-validating...")

            merged_content = self._merge_snippet(current_file_content, fixed_snippet)
            write_success = self._write_output_file(file_path, merged_content, overwrite=True)

            if write_success:
                logger.info(f"Successfully wrote fixed code to {file_path}")
                # Re-run validations after applying the fix
                try:
                    logger.info(f"Re-running validations for {file_path} after test failure remediation...")
                    # Retrieve the last used test command and cwd
                    test_command = self._current_task_results.get('last_test_command', ['pytest', 'tests/'])
                    cwd = self._current_task_results.get('last_test_cwd', self.context.base_path)

                    return_code, new_stdout, new_stderr = self.execute_tests(test_command, cwd)
                    self._current_task_results['test_stdout'] = new_stdout
                    self._current_task_results['test_stderr'] = new_stderr
                    self._current_task_results['test_results'] = self._parse_test_results(new_stdout) # Update test results

                    # Re-run other validations on the merged content
                    code_review_result = self.code_review_agent.analyze_python(merged_content) # Correct call
                    ethical_result = self.ethical_governance_engine.enforce_policy(merged_content, self.default_policy_config) # Correct call
                    self._current_task_results['code_review_results'] = code_review_result
                    self._current_task_results['ethical_analysis_results'] = ethical_result

                    logger.info(f"Validations re-run after test failure remediation.")
                    # The calling loop will re-generate and re-evaluate the grade report

                except Exception as e:
                    logger.error(f"Error occurred during re-validation after test failure remediation: {e}", exc_info=True)
                    # Update results with error status
                    self._current_task_results['test_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                    self._current_task_results['code_review_results'] = {'status': 'error', 'message': f"Re-validation error: {e}"}
                    self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': f"Re-validation error: {e}"}

                return True # Remediation was attempted and write succeeded

            else:
                logger.error(f"Failed to write fixed code to {file_path}. Aborting test failure remediation.")
                return False # Remediation attempt failed (write failed)

        except json.JSONDecodeError:
            logger.error("Failed to parse grade report JSON for test failure remediation.")
            return False
        except Exception as e:
            logger.error(f"Error during test failure remediation: {e}", exc_info=True)
            return False