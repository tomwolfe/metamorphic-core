import logging
import html
import os
import json
from pathlib import Path
from src.core.llm_orchestration import EnhancedLLMOrchestrator
import re
from unittest.mock import MagicMock
from src.cli.write_file import write_file # Ensure write_file is imported
import subprocess # Import subprocess for execute_tests
from src.core.agents.code_review_agent import CodeReviewAgent # Import CodeReviewAgent
from src.core.ethics.governance import EthicalGovernanceEngine # Import EthicalGovernanceEngine
from datetime import datetime # Import datetime for report timestamp
import uuid # Import uuid for temporary file naming

logger = logging.getLogger(__name__) # Corrected logger name

# Define a maximum file size for reading (e.g., 1MB)
MAX_READ_FILE_SIZE = 1024 * 1024 # 1 MB

# Define the marker for code insertion
METAMORPHIC_INSERT_POINT = "# METAMORPHIC_INSERT_POINT"

# Define maximum remediation attempts
MAX_REMEDIATION_ATTEMPTS = 2 # NEW CONSTANT

class Context:
    def __init__(self, base_path): # Corrected __init__
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

        if not isinstance(relative_path, str): # Added check for non-string
             logger.warning(f"Attempted to resolve path with non-string input: {relative_path}")
             return None

        if relative_path == "":
             # An empty string relative path should resolve to the base path itself
             return str(self._resolved_base_path)

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
    def __init__(self, context: Context): # Corrected __init__
        self.context = context
        self.tasks = [] # Will be loaded by start_workflow
        self._current_task_results = {} # Dictionary to store results for the current task iteration # ADDED


        # Initialize LLM Orchestrator - Pass placeholder dependencies for now
        self.llm_orchestrator = EnhancedLLMOrchestrator(
            kg=MagicMock(),
            spec=MagicMock(),
            ethics_engine=MagicMock()
        )
        # Instantiate CodeReviewAgent
        self.code_review_agent = CodeReviewAgent()

        # Instantiate EthicalGovernanceEngine and load default policy # ADDED BLOCK
        self.ethical_governance_engine = EthicalGovernanceEngine()
        self._load_default_policy() # Extract policy loading to a separate method
        # END ADDED BLOCK

    def _load_default_policy(self):
        """Load the default ethical policy from file."""
        # Use context.get_full_path for safety when loading the policy file
        # Assuming the policy file is relative to the base path, e.g., "policies/policy_bias_risk_strict.json"
        # If the policy path is absolute or outside the base path, get_full_path will return None.
        default_policy_relative_path = "policies/policy_bias_risk_strict.json" # Example relative path
        default_policy_path = self.context.get_full_path(default_policy_relative_path)

        if default_policy_path:
            try:
                self.default_policy_config = self.ethical_governance_engine.load_policy_from_json(default_policy_path)
                logger.info(f"Loaded default ethical policy: {self.default_policy_config.get('policy_name')}")
            except Exception as e:
                logger.error(f"Failed to load default ethical policy from {default_policy_path}: {e}", exc_info=True)
                self.default_policy_config = None # Set to None if loading fails
        else:
            # This warning is now correctly placed if path resolution fails
            logger.warning(f"Could not resolve path for default ethical policy '{default_policy_relative_path}'. Ethical analysis may be impacted.")
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
            logger.error(f"Failed to load roadmap from {self.roadmap_path}: {e}",
                         exc_info=True)
            return # Exit if roadmap loading fails
        self.context = context  # Update context if needed (though it's set in __init__)
        logger.info(f"Workflow initiated with roadmap: {roadmap_path}, output: {output_dir}")
        self.autonomous_loop()

    def autonomous_loop(self):
        """
        Main control flow loop for the autonomous Driver LLM.

        This method orchestrates the task selection, planning, agent invocation,
        and file management steps to drive the development process autonomously.
        It now includes automated remediation for code style and ethical issues.
        """
        if not hasattr(self, 'roadmap_path') or (self.roadmap_path is None):
            logger.error("Roadmap path not set. Cannot start autonomous loop.")
            return

        while True:
            logger.info('Starting autonomous loop iteration')
            self._current_task_results = {}

            try:
                full_roadmap_path = self.context.get_full_path(self.roadmap_path)
                if full_roadmap_path is None:
                    logger.error(f"Invalid roadmap path provided: {self.roadmap_path}. Cannot continue autonomous loop.")
                    break
                # Reload roadmap at the start of each iteration to get updated statuses
                self.tasks = self.load_roadmap(full_roadmap_path)
            except Exception as e:
                logger.error(f"Failed to reload roadmap from {self.roadmap_path}: {e}", exc_info=True)
                break # Exit loop on roadmap reload failure

            next_task = self.select_next_task(self.tasks)

            if next_task:
                task_id = next_task.get('task_id', 'Unknown ID')
                logger.info(f'Selected task: ID={task_id}')

                solution_plan = self.generate_solution_plan(next_task)
                logger.info(f'Generated plan: {solution_plan}')

                if solution_plan:
                    logger.info(f"Executing plan for task {task_id} with {len(solution_plan)} steps.")
                    code_written_in_iteration = False
                    last_written_filepath = None # Track the last file written to for remediation
                    last_written_content = None # Track the content written for remediation

                    for step_index, step in enumerate(solution_plan):
                        logger.info(f"Executing step {step_index + 1}/{len(solution_plan)}: {step}")

                        step_lower = step.lower()
                        code_generation_keywords = ["implement", "generate code", "write function", "modify file", "add logic to"]
                        file_writing_keywords = ["write file", "create file", "save to file", "output file", "generate file", "write output to"]
                        test_execution_keywords = ["run tests", "execute tests", "verify tests", "pytest", "test suite"]

                        # Improved filepath extraction: look for common file extensions anywhere in the step
                        filepath_match = re.search(r'(\S+\.(py|md|json|txt|yml|yaml|sh))', step, re.IGNORECASE) # Added .sh
                        filepath_from_step = filepath_match.group(1) if filepath_match else None

                        is_step_explicitly_file_writing = (filepath_from_step is not None) or any(keyword in step_lower for keyword in file_writing_keywords)
                        needs_coder_llm = any(keyword in step_lower for keyword in code_generation_keywords)
                        is_test_execution_step = any(keyword in step_lower for keyword in test_execution_keywords)

                        # Determine the target file for the step
                        filepath_to_use = next_task.get('target_file') # Start with task's target file
                        if not filepath_to_use and (is_step_explicitly_file_writing or needs_coder_llm) and filepath_from_step:
                            # If task has no target_file, but step mentions one and involves writing/generating
                            filepath_to_use = filepath_from_step
                        # If step is file writing but no specific file is mentioned, maybe skip or log warning?
                        # For now, we require a filepath if it's a file writing/code gen step.
                        if (is_step_explicitly_file_writing or needs_coder_llm) and not filepath_to_use:
                            logger.warning(f"Step {step_index + 1} identified as file writing/code gen but no target file specified in task or step: '{step}'. Skipping file operation.")
                            continue # Skip to the next step

                        generated_output = None
                        content_to_write = None
                        overwrite_file = False # Default to False for explicit writes unless specified

                        if is_test_execution_step:
                            logger.info(f"Step identified as test execution. Running tests for step: {step}")
                            test_command = ["pytest"]
                            # If a target file is specified and looks like a test file, use it
                            if filepath_to_use and "test_" in Path(filepath_to_use).name.lower():
                                test_command.append(filepath_to_use)
                            else:
                                # Otherwise, run all tests in the tests/ directory
                                test_command.append("tests/")
                            try:
                                return_code, stdout, stderr = self.execute_tests(test_command, self.context.base_path)
                                test_results = self._parse_test_results(stdout)
                                self._current_task_results['test_results'] = test_results
                                logger.info(f"Test Execution Results: Status={test_results['status']}, Passed={test_results['passed']}, Failed={test_results['failed']}, Total={test_results['total']}")
                                if test_results['status'] == 'failed':
                                    logger.error(f"Tests failed for step: {step}. Raw stderr:\n{stderr}")
                                elif test_results['status'] == 'error':
                                    logger.error(f"Test execution or parsing error for step: {step}. Message: {test_results['message']}. Raw stderr:\n{stderr}")
                            except Exception as e:
                                logger.error(f"An unexpected error occurred during command execution: {e}", exc_info=True)
                                self._current_task_results['test_results'] = {'status': 'error', 'passed': 0, 'failed': 0, 'total': 0, 'message': str(e)}

                        elif needs_coder_llm and filepath_to_use:
                            logger.info(f"Step identified as code generation for file {filepath_to_use}. Orchestrating read-generate-merge-write.")
                            existing_content = self._read_file_for_context(filepath_to_use)
                            coder_prompt = self._build_coder_prompt(next_task, step, filepath_to_use, existing_content)
                            logger.debug("Invoking Coder LLM with prompt: %s", coder_prompt[:500])
                            generated_snippet = self._invoke_coder_llm(coder_prompt)

                            if generated_snippet:
                                logger.info(f"Coder LLM generated snippet (first 100 chars): {generated_snippet[:100]}...")
                                merged_content = self._merge_snippet(existing_content, generated_snippet)
                                logger.debug("Snippet merged.")
                                logger.info(f"Attempting to write merged content to {filepath_to_use}.")
                                try:
                                    # Code generation steps typically overwrite the target file
                                    if self._write_output_file(filepath_to_use, merged_content, overwrite=True):
                                        logger.info(f"Successfully wrote merged content to {filepath_to_use}.")
                                        code_written_in_iteration = True
                                        last_written_filepath = filepath_to_use # Track last written file
                                        last_written_content = merged_content # Track the content written for remediation
                                        # *** FIX APPLIED HERE ***
                                        self._run_post_write_validation(filepath_to_use, merged_content, run_code_review=True, run_ethical_analysis=True) # Run validation
                                    else:
                                         logger.error(f"Failed to write merged content to {filepath_to_use} (write_output_file returned False).")
                                except FileExistsError:
                                    # This case should ideally not happen with overwrite=True, but log it
                                    logger.error(f"Unexpected FileExistsError when writing merged content to {filepath_to_use} with overwrite=True.")
                                except Exception as e:
                                    logger.error(f"Failed to write merged content to {filepath_to_use}: {e}", exc_info=True)
                            else:
                                logger.warning(f"Coder LLM returned empty or None snippet for step {step_index + 1}. Skipping file write.")

                        elif is_step_explicitly_file_writing and not needs_coder_llm and filepath_to_use:
                            logger.info(f"Step identified as file writing (non-code-gen). Processing file operation for step: {step}")
                            # For non-code-gen file writes, we might need a different approach
                            # (e.g., prompt LLM for file content based on step, or just create empty file)
                            # For now, using placeholder or skipping if content isn't generated.
                            # If the step implies creating a new file, overwrite=False might be appropriate initially.
                            # If it implies modifying an existing config/data file, need to read/merge.
                            # This is a simplified placeholder. A real system would need more logic here.
                            content_to_write = f"# Placeholder content for step: {step}\n" # Added newline
                            logger.info(f"Using placeholder content for file: {filepath_to_use}")
                            logger.info(f"Attempting to write file: {filepath_to_use}")
                            try:
                                # Decide overwrite based on step intent, default to False if not clear
                                # For a generic "write file" step, creating it if it doesn't exist seems reasonable.
                                if self._write_output_file(filepath_to_use, content_to_write, overwrite=False):
                                     logger.info(f"Successfully wrote placeholder content to {filepath_to_use}.")
                                     # Decide if validation is needed for non-code files
                                     # self._run_post_write_validation(filepath_to_use, content_to_write, run_code_review=False, run_ethical_analysis=False) # Example: no validation
                                     # We don't track last_written_filepath/content for remediation here, as it's not code gen
                                else:
                                     logger.error(f"Failed to write placeholder content to {filepath_to_use} (write_output_file returned False).")
                            except FileExistsError:
                                logger.warning(f"File {filepath_to_use} already exists. Skipping write as overwrite=False.")
                            except Exception as e:
                                logger.error(f"Failed to write file {filepath_to_use}: {e}", exc_info=True)

                        else:
                            logger.info(f"Step not identified as code generation, file writing, or test execution. Skipping agent invocation/file write for step: {step}")
                            # Potentially handle other step types here (e.g., "research X", "design Y")
                            pass # Continue to the next step without file operations

                    # --- Initial Grade Report Generation and Evaluation ---
                    # Only generate report if there was a file written that needs validation
                    if code_written_in_iteration and last_written_filepath:
                        logger.info("Generating initial Grade Report...")
                        grade_report_json = self.generate_grade_report(task_id, self._current_task_results)
                        logger.info(f"--- GRADE REPORT for Task {task_id} ---\n{grade_report_json}\n--- END GRADE REPORT ---")
                        evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                        recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                        logger.info(f"Initial Grade Report Evaluation: Recommended Action='{recommended_action}', Justification='{evaluation_result.get('justification')}'")

                        # --- Automated Remediation Loop (Task 1.7.4) ---
                        remediation_attempts = 0
                        final_evaluation_result = evaluation_result # Store initial evaluation

                        # Check if remediation is needed and possible based on the initial report
                        needs_remediation, remediation_type, feedback = self._check_if_remediation_needed(grade_report_json)

                        # Only attempt remediation if needed, code was written, and we know which file
                        if needs_remediation and code_written_in_iteration and last_written_filepath:
                            logger.info(f"Initiating automated remediation for {remediation_type} issues in {last_written_filepath}...")

                            while remediation_attempts < MAX_REMEDIATION_ATTEMPTS:
                                remediation_attempts += 1
                                logger.info(f"Remediation Attempt {remediation_attempts}/{MAX_REMEDIATION_ATTEMPTS}...")

                                # 1. Construct feedback prompt
                                remediation_prompt = self._build_remediation_prompt(
                                    task=next_task,
                                    target_file=last_written_filepath,
                                    original_code=last_written_content, # Use the content that was last written
                                    feedback=feedback,
                                    remediation_type=remediation_type
                                )

                                # 2. Invoke Coder LLM
                                logger.debug("Invoking Coder LLM for remediation...")
                                revised_snippet = self._invoke_coder_llm(remediation_prompt)

                                if not revised_snippet:
                                    logger.warning("Remediation failed: Coder LLM returned empty snippet.")
                                    # Use the last evaluation result before breaking
                                    # final_evaluation_result remains the evaluation from the last successful step/attempt
                                    break # Exit remediation loop

                                # 3. Merge and Write revised code
                                # Read the *current* content again before merging the snippet
                                # This is important if subsequent steps modified the file *after* the initial write
                                # but *before* remediation starts.
                                current_content_before_remediation_write = self._read_file_for_context(last_written_filepath)
                                if current_content_before_remediation_write is None: # Handle read failure
                                     logger.error(f"Remediation failed: Could not read current content of {last_written_filepath} before merging revised snippet.")
                                     break # Exit remediation loop

                                revised_content = self._merge_snippet(current_content_before_remediation_write, revised_snippet)
                                try:
                                    if not self._write_output_file(last_written_filepath, revised_content, overwrite=True):
                                         logger.error(f"Remediation failed: Could not write revised content to {last_written_filepath}.")
                                         # final_evaluation_result remains the evaluation from the last successful step/attempt
                                         break # Exit remediation loop
                                    logger.info(f"Successfully wrote remediated content to {last_written_filepath}.")
                                    last_written_content = revised_content # Update tracked content for potential next attempt
                                except Exception as write_err:
                                    logger.error(f"Remediation failed: Error writing revised content: {write_err}", exc_info=True)
                                    # final_evaluation_result remains the evaluation from the last successful step/attempt
                                    break # Exit remediation loop

                                # 4. Re-run specific validation
                                logger.info(f"Re-running {remediation_type} validation...")
                                # Clear previous validation results for the specific type before re-running
                                if remediation_type == "Code Style":
                                     self._current_task_results.pop('code_review_results', None)
                                     self._run_post_write_validation(last_written_filepath, revised_content, run_code_review=True, run_ethical_analysis=False)
                                elif remediation_type == "Ethical Transparency":
                                     self._current_task_results.pop('ethical_analysis_results', None)
                                     self._run_post_write_validation(last_written_filepath, revised_content, run_code_review=False, run_ethical_analysis=True)
                                # Note: _run_post_write_validation updates self._current_task_results

                                # 5. Re-generate and Re-evaluate Grade Report
                                logger.info("Generating updated Grade Report after remediation attempt...")
                                # Need to regenerate the *full* grade report using the potentially updated results
                                grade_report_json = self.generate_grade_report(task_id, self._current_task_results) # Use updated results
                                logger.info(f"--- UPDATED GRADE REPORT (Attempt {remediation_attempts}) ---\n{grade_report_json}\n--- END UPDATED GRADE REPORT ---")
                                evaluation_result = self._parse_and_evaluate_grade_report(grade_report_json)
                                recommended_action = evaluation_result.get("recommended_action", "Manual Review Required")
                                logger.info(f"Remediation Attempt {remediation_attempts} Evaluation: Recommended Action='{recommended_action}', Justification='{evaluation_result.get('justification')}'")

                                final_evaluation_result = evaluation_result # Store the latest evaluation

                                # 6. Check if remediation succeeded based on the *new* report
                                needs_remediation, remediation_type, feedback = self._check_if_remediation_needed(grade_report_json)
                                if not needs_remediation:
                                    logger.info("Remediation successful.")
                                    break # Exit remediation loop

                                if remediation_attempts >= MAX_REMEDIATION_ATTEMPTS:
                                    logger.warning("Maximum remediation attempts reached.")
                                    break # Exit remediation loop
                        else:
                             # Log if remediation was recommended by evaluation but not possible (e.g., no code written)
                             if evaluation_result.get("recommended_action") == "Regenerate Code":
                                  logger.warning("Evaluation recommended regeneration, but no code was written in this iteration or target file is unknown. Skipping automated remediation.")
                             else:
                                  logger.info("No remediation needed or possible for Code Style/Ethical issues based on initial evaluation.")
                        # --- End Remediation Loop ---
                    else:
                         # Log if no code was written and thus no initial report/remediation attempt
                         logger.info("No code was written in this iteration. Skipping grade report and remediation.")
                         # The final evaluation result remains the initial evaluation result (if any) or default


                    # --- Final Roadmap Update ---
                    # Use the final evaluation result (either initial or after remediation)
                    final_recommended_action = final_evaluation_result.get("recommended_action", "Manual Review Required")
                    new_status = next_task['status'] # Start with current status

                    # Update status based on the final evaluation
                    if final_recommended_action == "Completed":
                        new_status = "Completed"
                    elif final_recommended_action == "Blocked":
                        new_status = "Blocked"
                    # If action is "Regenerate Code" or "Manual Review Required", status remains "Not Started"
                    # unless the task definition implies otherwise or we add more complex state logic.
                    # For now, stick to Completed/Blocked updates.

                    if new_status != next_task['status']:
                        logger.info(f"Updating task status from '{next_task['status']}' to '{new_status}' for task {task_id}")
                        try:
                            full_roadmap_path = self.context.get_full_path(self.roadmap_path)
                            if full_roadmap_path:
                                try:
                                    # Read the latest roadmap content *before* modifying
                                    with open(full_roadmap_path, 'r') as f:
                                        roadmap_data = json.load(f)
                                except FileNotFoundError:
                                    logger.error(f"Error updating roadmap status for task {task_id}: Roadmap file not found at {full_roadmap_path}")
                                    # Continue loop, but status wasn't saved
                                    continue
                                except json.JSONDecodeError:
                                     logger.error(f"Error updating roadmap status for task {task_id}: Invalid JSON in roadmap file at {full_roadmap_path}")
                                     # Continue loop, but status wasn't saved
                                     continue


                                task_found = False
                                if isinstance(roadmap_data, dict) and isinstance(roadmap_data.get('tasks'), list):
                                    for task_entry in roadmap_data['tasks']:
                                        # Use get() with default None for safety
                                        if isinstance(task_entry, dict) and task_entry.get('task_id') == task_id:
                                            task_entry['status'] = new_status
                                            task_found = True
                                            break

                                if task_found:
                                    if self._safe_write_roadmap_json(self.roadmap_path, roadmap_data):
                                        logger.info(f"Successfully updated status for task {task_id} in {self.roadmap_path}")
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
                else:
                    logger.warning(f"No solution plan generated for task {task_id}. Skipping task execution.")
                    # Should we mark the task as blocked or require manual review if plan generation fails?
                    # For now, it remains 'Not Started' and might be selected again.

            else:
                logger.info('No tasks available in Not Started status or dependencies not met. Exiting autonomous loop.')
                break # Exit the while loop if no task is selected

        logger.info('Autonomous loop terminated.')

    # --- Helper method to build coder prompt ---
    def _build_coder_prompt(self, task: dict, step: str, filepath: str, existing_content: str) -> str:
        """Builds the prompt for the Coder LLM."""
        # Ensure inputs are strings, handle None gracefully
        task_name = task.get('task_name', 'Unknown Task') if isinstance(task, dict) else 'Unknown Task'
        description = task.get('description', 'No description provided.') if isinstance(task, dict) else 'No description provided.'
        step_str = str(step) if step is not None else 'No step description.'
        filepath_str = str(filepath) if filepath is not None else 'an unspecified file'
        existing_content_str = str(existing_content) if existing_content is not None else ''

        return f"""You are a Coder LLM expert in Python.
Your task is to generate only the code snippet required to implement the following specific step from a larger development plan.

Overall Task: "{task_name}"
Task Description: {description}

Specific Plan Step:
{step_str}

The primary file being modified is {filepath_str}.

EXISTING CONTENT OF {filepath_str}:

{existing_content_str}

Generate only the Python code snippet needed to fulfill the "Specific Plan Step". Do not include any surrounding text, explanations, or markdown code block fences (```). Provide just the raw code lines that need to be added or modified.
"""


    # --- Helper method to run post-write validation ---
    def _run_post_write_validation(self, filepath: str, content: str, run_code_review=True, run_ethical_analysis=True):
         """Runs code review and/or ethical analysis and updates results."""
         # Ensure inputs are strings, handle None gracefully
         filepath_str = str(filepath) if filepath is not None else 'Unknown file'
         content_str = str(content) if content is not None else ''

         if run_code_review:
             try:
                 logger.info(f"Running code review and security scan for {filepath_str}...")
                 # Assuming analyze_python takes content string directly
                 review_results = self.code_review_agent.analyze_python(content_str)
                 self._current_task_results['code_review_results'] = review_results
                 logger.info(f"Code Review and Security Scan Results for {filepath_str}: {review_results}")
             except Exception as review_e:
                 logger.error(f"Error running code review/security scan for {filepath_str}: {review_e}", exc_info=True)
                 self._current_task_results['code_review_results'] = {'status': 'error', 'message': str(review_e)}

         if run_ethical_analysis:
             if self.default_policy_config:
                 try:
                     logger.info(f"Running ethical analysis for {filepath_str}...")
                     # Assuming enforce_policy takes content string and policy config
                     ethical_analysis_results = self.ethical_governance_engine.enforce_policy(content_str, self.default_policy_config)
                     self._current_task_results['ethical_analysis_results'] = ethical_analysis_results
                     logger.info(f"Ethical Analysis Results for {filepath_str}: {ethical_analysis_results}")
                 except Exception as ethical_e:
                     logger.error(f"Error running ethical analysis for {filepath_str}: {ethical_e}", exc_info=True)
                     self._current_task_results['ethical_analysis_results'] = {'overall_status': 'error', 'message': str(ethical_e)}
             else:
                 logger.warning("Default ethical policy not loaded. Skipping ethical analysis.")
                 self._current_task_results['ethical_analysis_results'] = {'overall_status': 'skipped', 'message': 'Default policy not loaded.'}

    # --- Helper method to check if remediation is needed ---
    def _check_if_remediation_needed(self, grade_report_json: str) -> tuple[bool, str | None, str | None]:
        """Checks the grade report if remediation is needed for Code Style or Ethical issues."""
        if not isinstance(grade_report_json, str):
             logger.warning(f"_check_if_remediation_needed received non-string input: {type(grade_report_json)}")
             return False, None, None

        try:
            report_data = json.loads(grade_report_json)
            # Re-evaluate the report to get the recommended action based on the *current* state
            evaluation = self._parse_and_evaluate_grade_report(grade_report_json)

            # Only remediate if evaluation suggests regeneration AND the reason is specifically style or ethical
            # The _parse_and_evaluate_grade_report method needs to provide more granular justification
            # or the check here needs to look directly at validation_results.
            # Let's refine this check to look at validation_results directly, as remediation is specific.

            validation_results = report_data.get('validation_results', {})
            code_review = validation_results.get('code_review', {})
            ethical_analysis = validation_results.get('ethical_analysis', {})

            # Check for Code Style issues (excluding security issues)
            if code_review.get('status') == 'failed':
                style_findings = [f for f in code_review.get('static_analysis', []) if not f.get('severity','').startswith('security')]
                if style_findings:
                    # Extract feedback for non-security issues
                    style_feedback = "\n".join([f"- {f.get('file', '')}:{f.get('line', '')}:{f.get('col', '')}: {f.get('code', '')} {f.get('message', '')}"
                                                for f in style_findings])
                    return True, "Code Style", f"Please fix the following code style issues:\n{style_feedback}"

            # Check for Ethical Transparency issues
            if ethical_analysis.get('overall_status') == 'rejected' and ethical_analysis.get('TransparencyScore', {}).get('status') == 'violation':
                feedback = ethical_analysis.get('TransparencyScore', {}).get('details', 'Missing required docstring(s).')
                return True, "Ethical Transparency", f"Please fix the following ethical transparency issue: {feedback}"

            # Check if the overall evaluation recommended regeneration for *other* reasons (like tests)
            # If the recommended action is Regenerate Code but it's not due to Style or Ethical issues checked above,
            # then remediation is not needed *for these specific types*.
            if evaluation.get("recommended_action") == "Regenerate Code":
                 # If we reach here, it means regeneration was recommended, but not for Style or Ethical Transparency.
                 # This might be due to test failures, security issues, or other factors.
                 # We only remediate Style and Ethical Transparency automatically.
                 pass # Fall through to return False

            return False, None, None # No specific style or transparency issues found for remediation

        except json.JSONDecodeError:
            logger.error("Failed to parse Grade Report JSON during remediation check.")
            return False, None, None
        except Exception as e:
            logger.error(f"Error checking grade report for remediation needs: {e}", exc_info=True)
            return False, None, None

    # --- Helper method to build remediation prompt ---
    def _build_remediation_prompt(self, task: dict, target_file: str, original_code: str, feedback: str, remediation_type: str) -> str:
        """Constructs a targeted prompt for the Coder LLM for remediation."""
        # Ensure inputs are strings, handle None gracefully
        task_name = task.get('task_name', 'Unknown Task') if isinstance(task, dict) else 'Unknown Task'
        target_file_str = str(target_file) if target_file is not None else 'an unspecified file'
        original_code_str = str(original_code) if original_code is not None else ''
        feedback_str = str(feedback) if feedback is not None else 'No specific feedback provided.'
        remediation_type_str = str(remediation_type) if remediation_type is not None else 'unknown'

        # Sanitize feedback before including it in the prompt
        sanitized_feedback = html.escape(feedback_str) # Basic HTML escaping

        return f"""You are a Coder LLM expert in Python, tasked with fixing specific issues in existing code based on validation feedback.
Overall Task: "{task_name}"
Target File: {target_file_str}

The following code in {target_file_str} failed validation for "{remediation_type_str}":

```python
{original_code_str}
```

Validation Feedback:
{sanitized_feedback}

Your task is to regenerate only the necessary parts of the code snippet to address the specific feedback provided above.
Focus only on fixing the reported {remediation_type_str} issues. Do not introduce other changes or refactor unrelated code.
Output *only* the corrected Python code snippet. Do not include explanations or markdown fences.
"""


    # --- Remaining methods (unchanged except for minor cleanup/safety) ---
    def _read_file_for_context(self, relative_file_path: str) -> str:
        """
        Reads content from a file, handling errors and size limits.

        Args:
            relative_file_path: The path to the file, relative to the context's base_path.

        Returns:
            The content of the file as a string, or an empty string if reading fails
            or the file exceeds the size limit. Returns None on critical path resolution failure.
        """
        if not isinstance(relative_file_path, str) or relative_file_path == "":
            logger.warning(f"Attempted to read file with invalid path: {relative_file_path}")
            return "" # Return empty string for invalid input

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
            with open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
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

        target_file_context = ""
        task_target_file = task.get('target_file')

        if task_target_file:
             target_file_context = f"The primary file being modified for this task is specified as `{task_target_file}` in the task metadata. Focus your plan steps on actions related to this file."


        planning_prompt = f"""You are an AI assistant specializing in software development workflows.
Your task is to generate a step-by-step solution plan for the following development task from the Metamorphic Software Genesis Ecosystem roadmap.

Task Name: {task_name}

Task Description:
{description}

{target_file_context}

Please provide the plan as a numbered markdown list. Do not include any introductory or concluding remarks outside the list.
When generating steps that involve modifying the primary file for this task, ensure you refer to the file identified in the context (e.g., src/core/automation/workflow_driver.py).
"""


        logger.debug(f"Sending planning prompt to LLM for task '{task_name}'.")

        llm_response = self._invoke_coder_llm(planning_prompt)

        if not llm_response:
            logger.warning(f"LLM returned empty response for plan generation for task '{task_name}'.")
            return []

        plan_steps = []
        # Updated regex to be more robust, allowing for potential leading/trailing whitespace
        step_pattern = re.compile(r'^\s*\d+[.:-]?\s*(.*)$', re.MULTILINE)


        current_step_text = None

        for line in llm_response.splitlines():
            match = step_pattern.match(line)
            if match:
                if current_step_text is not None:
                    plan_steps.append(current_step_text.strip())
                current_step_text = match.group(1).strip()
            elif current_step_text is not None:
                # Append subsequent lines to the current step, preserving some structure
                # Add a space unless the line starts with punctuation that shouldn't have a preceding space
                separator = " "
                if line.strip() and line.strip()[0] in [',', '.', ';', ':', ')', ']']:
                     separator = ""
                current_step_text += separator + line.strip()
            # Ignore lines that don't match the pattern and aren't part of a multi-line step

        if current_step_text is not None:
            plan_steps.append(current_step_text.strip())

        # Basic sanitization: remove markdown emphasis characters
        sanitized_steps = [re.sub(r'[*_`]', '', step).strip() for step in plan_steps]
        # Filter out any empty steps that might result from parsing
        sanitized_steps = [step for step in sanitized_steps if step]


        logger.debug(f"Parsed and sanitized plan steps: {sanitized_steps}")

        return sanitized_steps

    def _invoke_coder_llm(self, coder_llm_prompt: str) -> str | None: # Added None to return type hint
        """
        Invokes the Coder LLM (LLMOrchestrator) to generate code or text.

        Args:
            coder_llm_prompt: The prompt to send to the Coder LLM.

        Returns:
            Return the generated text from the LLM, or None if there was an error.
        """
        if not isinstance(coder_llm_prompt, str) or coder_llm_prompt.strip() == "":
             logger.warning("Attempted to invoke Coder LLM with empty or invalid prompt.")
             return None
        try:
            # Assuming self.llm_orchestrator.generate handles the actual LLM call
            response = self.llm_orchestrator.generate(coder_llm_prompt)

            if response is None:
                logger.error("LLM Orchestrator generate method returned None.")
                return None

            # Clean markdown code block fences if present
            cleaned_response = response.strip()
            # Use regex for more robust removal of code block fences and language specifiers
            cleaned_response = re.sub(r'^```[\w\s]*\n', '', cleaned_response, count=1)
            cleaned_response = re.sub(r'\n```$', '', cleaned_response, count=1)


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

        task_status_map = {
            task.get('task_id'): task.get('status')
            for task in tasks if isinstance(task, dict) and 'task_id' in task and 'status' in task
        }

        # Sort tasks by priority (assuming 'priority' is a comparable type, e.g., number or string like 'High', 'Medium', 'Low')
        # If priority is a string, you might need a mapping or custom sort key.
        # For simplicity, let's assume a simple sort works or add a mapping.
        # Example mapping: {'High': 1, 'Medium': 2, 'Low': 3}
        priority_order = {'High': 1, 'Medium': 2, 'Low': 3}
        # Use a stable sort key that puts unknown priorities last
        sorted_tasks = sorted(tasks, key=lambda t: priority_order.get(t.get('priority', 'Low'), 99))


        for task in sorted_tasks: # Iterate through sorted tasks
            if not isinstance(task, dict) or 'task_id' not in task or 'status' not in task or 'description' not in task or 'priority' not in task:
                logger.warning(f"Skipping invalid task format in list: {task}")
                continue

            task_id = task.get('task_id')
            # Using the corrected _is_valid_task_id method
            if not self._is_valid_task_id(task_id):
                logger.warning(f"Skipping task with invalid task_id format: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue

            if task['status'] == 'Not Started':
                depends_on = task.get('depends_on', [])

                if not isinstance(depends_on, list):
                    logger.warning(f"Skipping task {task_id}: 'depends_on' field is not a list.")
                    continue

                all_dependencies_completed = True
                for dep_task_id in depends_on:
                    if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                        logger.warning(f"Skipping task {task_id}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                        all_dependencies_completed = False
                        break

                    dep_status = task_status_map.get(dep_task_id)

                    if dep_status is None:
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' not found in roadmap.")
                        all_dependencies_completed = False
                        break
                    elif dep_status != 'Completed':
                        logger.debug(f"Skipping task {task_id}: Dependency '{dep_task_id}' status is '{dep_status}' (requires 'Completed').")
                        all_dependencies_completed = False
                        break

                if all_dependencies_completed:
                    return task # Return the highest priority task that is 'Not Started' and has completed dependencies

        return None # No suitable task found

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
        return [prompt] # Return as a list for consistency, though only one prompt is generated here

    def generate_user_actionable_steps(self, steps):
        if not isinstance(steps, list):
            raise TypeError("generate_user_actionable_steps expects a list of strings")
        if not all(isinstance(step, str) for step in steps):
            raise TypeError("generate_user_actionable_steps expects a list of strings")

        if not steps:
            return ""

        markdown_steps = ""
        for i, step in enumerate(steps):
            markdown_steps += f"{i + 1}. - [ ] {html.escape(step)}\n"
        return markdown_steps

    def load_roadmap(self, roadmap_file_path):
        tasks = []
        max_file_size = 20000 # Keep size limit
        if roadmap_file_path is None:
            logger.error(f"Failed to load roadmap from None: roadmap_file_path is None")
            return tasks
        full_roadmap_path = roadmap_file_path # This is already resolved by the caller (start_workflow or autonomous_loop)

        if not os.path.exists(full_roadmap_path):
            logger.error(f"ROADMAP.json file not found at path: {full_roadmap_path}")
            return tasks

        if not os.path.isfile(full_roadmap_path):
             logger.error(f"Roadmap path is not a file: {full_roadmap_path}")
             return tasks

        try:
            file_size = os.path.getsize(full_roadmap_path)
            if file_size > max_file_size:
                logger.error(
                f"ROADMAP.json file exceeds maximum allowed size of {max_file_size} bytes ({file_size} bytes).")
                return tasks
        except Exception as e:
             logger.error(f"Error checking roadmap file size {full_roadmap_path}: {e}", exc_info=True)
             return tasks


        try:
            with open(full_roadmap_path, 'r', encoding='utf-8') as f: # Specify encoding
                roadmap_data = json.load(f)
        except json.JSONDecodeError:
            logger.error(f"Invalid JSON in roadmap file: {full_roadmap_path}")
            return tasks
        except Exception as e:
             logger.error(f"Unexpected error reading roadmap file {full_roadmap_path}: {e}", exc_info=True)
             return tasks


        if not isinstance(roadmap_data, dict):
             logger.error(f"Invalid roadmap format: Root is not a dictionary in {full_roadmap_path}.")
             return tasks

        if 'tasks' not in roadmap_data:
            logger.error("ROADMAP.json must contain a 'tasks' key.")
            return tasks

        if not isinstance(roadmap_data['tasks'], list):
            logger.error("'tasks' must be a list in ROADMAP.json.")
            return tasks

        for task_data in roadmap_data['tasks']:
            if not isinstance(task_data, dict):
                logger.warning(f"Skipping invalid task (not a dictionary) in {full_roadmap_path}: {task_data}")
                continue

            required_keys = ['task_id', 'priority', 'task_name', 'status', 'description']
            if not all(key in task_data for key in required_keys):
                logger.warning(f"Task missing required keys in {full_roadmap_path}: {task_data}. Required keys are: {required_keys}")
                continue

            task_id = task_data.get('task_id') # Use get for safety, though check is done above
            # Using the corrected _is_valid_task_id method
            if not self._is_valid_task_id(task_id):
                logger.warning(
                f"Skipping task with invalid task_id format in {full_roadmap_path}: '{task_id}'. Task IDs can only contain alphanumeric characters, underscores, and hyphens.")
                continue

            task_name = task_data.get('task_name')
            if len(task_name) > 150:
                logger.warning(f"Task Name '{task_name}' exceeds 150 characters in {full_roadmap_path}. Task will be skipped.")
                continue

            task_description = task_data.get('description')
            escaped_description = html.escape(task_description) # Escape description

            depends_on = task_data.get('depends_on', [])
            if not isinstance(depends_on, list):
                logger.warning(f"Skipping task {task_id} in {full_roadmap_path}: 'depends_on' field is not a list.")
                continue

            is_depends_on_valid = True
            validated_depends_on = []
            for dep_task_id in depends_on:
                # Using the corrected _is_valid_task_id method
                if not isinstance(dep_task_id, str) or not self._is_valid_task_id(dep_task_id):
                    logger.warning(f"Skipping task {task_id} in {full_roadmap_path}: Invalid task_id '{dep_task_id}' found in 'depends_on' list.")
                    is_depends_on_valid = False
                    break
                validated_depends_on.append(dep_task_id)

            if not is_depends_on_valid:
                continue

            task = {
                'task_id': task_id,
                'priority': task_data.get('priority'), # Use get for safety
                'task_name': task_name,
                'status': task_data.get('status'), # Use get for safety
                'description': escaped_description,
                'target_file': task_data.get('target_file'),
                'depends_on': validated_depends_on
            }
            tasks.append(task)
        return tasks

    # Corrected method name to match usage in load_roadmap and select_next_task
    def _is_valid_task_id(self, task_id):
        """Validates task_id to ensure it only contains allowed characters and format."""
        if not isinstance(task_id, str):
            return False
        # Updated regex to allow hyphens and underscores, and require at least one char
        # The original regex `^[a-zA-Z0-9][a-zA-Z0-9-]$` only allowed a 2-character ID starting with alphanumeric, followed by alphanumeric or hyphen.
        # A more typical ID regex might be:
        return bool(re.fullmatch(r'^[a-zA-Z0-9_-]+$', task_id))


    def file_exists(self, relative_file_path):
        """Checks if a file exists in the workspace using the context's base path."""
        if not isinstance(relative_file_path, str):
            logger.warning(f"file_exists received non-string input: {type(relative_file_path)}")
            return False
        try:
            full_path = self.context.get_full_path(relative_file_path)
            if full_path is None:
                logger.warning(f"Failed to resolve path for existence check: {relative_file_path}")
                return False
            resolved_path = Path(full_path)
        except Exception as e:
            logger.error(f"Error resolving filepath {relative_file_path} for existence check: {e}",
                         exc_info=True)
            return False

        return os.path.exists(resolved_path) and os.path.isfile(resolved_path)

    def list_files(self):
        """Lists files and directories in the workspace root."""
        base_path = self.context.base_path
        entries = []
        try:
            resolved_base_path_str = self.context.get_full_path("") # Use empty string to get resolved base path
            if resolved_base_path_str is None:
                logger.error(f"Failed to resolve base path for listing: {base_path}")
                return []
            resolved_base_path = Path(resolved_base_path_str)

            if not resolved_base_path.is_dir():
                logger.error(f"Base path is not a valid directory: {base_path}")
                return []

            for name in os.listdir(resolved_base_path):
                # Basic check to skip hidden files/dirs and potentially unsafe names
                if name.startswith('.') or not self._is_valid_filename(name):
                    logger.debug(f"Skipping listing of filename: {name}") # Changed to debug, warning might be too noisy
                    continue

                full_path = resolved_base_path / name

                # Use lstat to avoid following symlinks if desired, or just stat
                # Using stat for simplicity here
                try:
                    stat_info = full_path.stat()
                    if full_path.is_file():
                        entries.append({'name': name, 'status': 'file', 'size': stat_info.st_size}) # Added size
                    elif full_path.is_dir():
                        entries.append({'name': name, 'status': 'directory'})
                except OSError as e:
                     logger.warning(f"Could not stat file/dir {full_path}: {e}")
                     continue # Skip entry if stat fails


        except Exception as e:
            logger.error(f"Error listing files in {base_path}: {e}", exc_info=True)
            return []
        return entries

    def _is_valid_filename(self, filename):
        """Basic validation for filenames to prevent listing malicious names."""
        if not isinstance(filename, str):
            return False
        # Allow alphanumeric, underscore, hyphen, dot. Prevent leading/trailing dots/hyphens. Prevent '..'.
        # This regex is stricter than the previous one which seemed incorrect.
        # It allows typical filenames like 'my_file.txt', 'my-file-1.0', 'archive.tar.gz'
        if '..' in filename or '/' in filename or '\\' in filename: # Check for path traversal attempts
            return False
        if filename in ['.', '..']:
            return False
        # Allow alphanumeric, underscore, hyphen, dot. Must contain at least one valid char.
        # Dots are allowed internally and for extensions, but not at start/end. Hyphens/underscores allowed internally.
        if not re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9._-]*[a-zA-Z0-9]$|^[a-zA-Z0-9]$', filename):
             # This regex is complex. A simpler approach might be:
             # return bool(re.fullmatch(r'^[a-zA-Z0-9._-]+$', filename)) and '..' not in filename and filename[0] != '.' and filename[-1] != '.'
             # Let's use a slightly more permissive but still safe version:
             if not re.fullmatch(r'^[a-zA-Z0-9][a-zA-Z0-9._-]*$', filename):
                  return False
             if filename.endswith('.'): # Prevent trailing dot
                  return False
             # Add check for common temporary file patterns if needed, but regex handles leading dot
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
            full_path = self.context.get_full_path(filepath)
            if full_path is None:
                logger.error(f"Failed to resolve path for writing: {filepath}")
                return False
            resolved_filepath = Path(full_path)
        except Exception as e:
            logger.error(f"Error resolving filepath {filepath} for writing: {e}", exc_info=True)
            return False

        parent_dir = resolved_filepath.parent
        if not parent_dir.exists():
            try:
                parent_dir.mkdir(parents=True, exist_ok=True)
                logger.info(f"Created directory: {parent_dir}")
            except Exception as e:
                logger.error(f"Failed to create directory {parent_dir}: {e}", exc_info=True)
                return False

        try:
            # write_file is assumed to handle the actual file writing with overwrite logic
            result = write_file(str(resolved_filepath), content, overwrite=overwrite)
            return result
        except FileExistsError as e:
            # Re-raise FileExistsError so the caller can handle it specifically
            raise e
        except FileNotFoundError as e:
            logger.error(f"File not found error when writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False
        except PermissionError as e:
            logger.error(f"Permission error when writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False
        except Exception as e:
            logger.error(f"Unexpected error writing to {filepath} (resolved: {resolved_filepath}): {e}", exc_info=True)
            return False

    def execute_tests(self, test_command: list[str], cwd: str) -> tuple[int, str, str]:
        stdout = ""
        stderr = ""
        return_code = 1

        if not isinstance(test_command, list) or not all(isinstance(arg, str) for arg in test_command) or not test_command:
             logger.error(f"Invalid test command format: {test_command}")
             return 1, "", "Invalid command format"

        if not isinstance(cwd, str) or not Path(cwd).is_dir():
             logger.error(f"Invalid current working directory: {cwd}")
             return 1, "", f"Invalid working directory: {cwd}"


        command_str = ' '.join(test_command)
        logger.info(f"Executing command: {command_str} in directory: {cwd}")

        try:
            # Use a reasonable timeout for test execution
            process = subprocess.run(
                test_command,
                cwd=cwd,
                capture_output=True,
                text=True,
                check=False, # Do not raise CalledProcessError on non-zero exit code
                timeout=300 # 5 minute timeout
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
        except TimeoutError:
            error_msg = f"Error: Command timed out after 300 seconds."
            stderr = error_msg
            return_code = 1 # Or a specific timeout code
            logger.error(error_msg)
        except Exception as e:
            error_msg = f"An unexpected error occurred during command execution: {e}"
            stderr = error_msg
            return_code = 1
            logger.error(error_msg)

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
        # Ensure inputs are strings, handle None gracefully
        existing_content_str = str(existing_content) if existing_content is not None else ''
        snippet_str = str(snippet) if snippet is not None else ''

        if not snippet_str:
            return existing_content_str # Return original content if snippet is empty

        marker_index = existing_content_str.find(METAMORPHIC_INSERT_POINT)

        if marker_index != -1:
            before_marker = existing_content_str[:marker_index]
            after_marker = existing_content_str[marker_index + len(METAMORPHIC_INSERT_POINT):]
            # Insert snippet, potentially adding a newline before/after if needed for formatting
            # Simple insertion:
            return before_marker + snippet_str + after_marker
        else:
            # Append snippet, ensuring there's a newline if the existing content isn't empty and doesn't end with one
            if not existing_content_str:
                return snippet_str
            if not existing_content_str.endswith('\n'):
                return existing_content_str + "\n" + snippet_str
            return existing_content_str + snippet_str # Append directly if existing content ends with newline

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
        if not isinstance(raw_output, str):
             logger.warning(f"_parse_test_results received non-string input: {type(raw_output)}")
             raw_output = "" # Treat as empty string

        if not raw_output.strip(): # Check after stripping whitespace
            logger.warning("Received empty output for test results parsing.")
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Received empty output.'}

        # Look for the final summary line which usually contains the counts
        # Example: "== 1 passed, 1 failed in 0.12s =="
        # Example: "== 1 error in 0.01s =="
        # Example: "== no tests ran in 0.01s =="
        summary_lines = [line for line in raw_output.splitlines() if line.strip().startswith('==') and ('test session' in line or 'passed' in line or 'failed' in line or 'skipped' in line or 'error' in line or 'no tests ran' in line)]

        if not summary_lines:
            logger.warning("Could not find pytest summary lines in output.")
            # Attempt to find counts even without summary lines as a fallback?
            # For now, return error if summary is missing.
            return {'passed': 0, 'failed': 0, 'total': 0, 'status': 'error', 'message': 'Could not find pytest summary lines in output.'}

        final_summary_line = summary_lines[-1]

        # Regex to find counts and their statuses (passed, failed, skipped, error)
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

        total = passed + failed + skipped + errors

        # Determine status
        status = 'error' # Default to error if parsing fails or no tests ran
        message = 'Could not parse test results output.'

        if total > 0:
            if failed == 0 and errors == 0:
                status = 'passed'
                message = 'All tests passed.'
            else:
                status = 'failed'
                message = 'Some tests failed or had errors.'
        elif "no tests ran" in final_summary_line:
             status = 'skipped' # Or a specific 'no_tests' status
             message = 'No tests were collected or run.'
        # If total is 0 and no "no tests ran" message, status remains 'error'

        results = {
            'passed': passed,
            'failed': failed,
            'total': total,
            'status': status,
            'message': message
        }

        logger.debug(f"Parsed test results: {results}")
        return results

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
        # Ensure inputs are valid
        task_id_str = str(task_id) if task_id is not None else 'Unknown Task ID'
        validation_results_dict = validation_results if isinstance(validation_results, dict) else {}

        report = {
            "task_id": task_id_str,
            "timestamp": datetime.utcnow().isoformat(),
            "validation_results": {
                "tests": validation_results_dict.get('test_results', {}),
                "code_review": validation_results_dict.get('code_review_results', {}),
                "ethical_analysis": validation_results_dict.get('ethical_analysis_results', {})
            },
            "grades": self._calculate_grades(validation_results_dict)
        }

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
        # Ensure validation_results is a dictionary
        validation_results_dict = validation_results if isinstance(validation_results, dict) else {}

        grades = {
            "non_regression": {"percentage": 0, "justification": "No non-regression tests executed."},
            "test_success": {"percentage": 0, "justification": "No test results available."},
            "code_style": {"percentage": 0, "justification": "No code review results available."},
            "ethical_policy": {"percentage": 0, "justification": "No ethical analysis results available."},
            "security_soundness": {"percentage": 0, "justification": "No security results available."}
        }

        # Test Success Grade (30%)
        test_results = validation_results_dict.get('test_results')
        if test_results and test_results.get('status') != 'error':
            total_tests = test_results.get('total', 0)
            passed_tests = test_results.get('passed', 0)
            if total_tests > 0:
                percentage = 100 * (passed_tests / total_tests)
                grades['test_success'] = {
                    "percentage": round(percentage),
                    "justification": f"Tests executed: {total_tests}, Passed: {passed_tests}, Failed: {test_results.get('failed', 0)}, Status: {test_results.get('status')}"
                }
            else: # total_tests is 0 but status is not error (e.g., skipped, no tests ran)
                 grades['test_success'] = {
                     "percentage": 100, # Consider 100% if no tests were applicable/run without error
                     "justification": f"No tests applicable or run. Status: {test_results.get('status')}. Message: {test_results.get('message', 'N/A')}"
                 }
        elif test_results and test_results.get('status') == 'error':
            grades['test_success'] = {
                "percentage": 0,
                "justification": f"Test execution or parsing error: {test_results.get('message', 'Unknown error')}"
            }

        # Code Style (10%) and Security Soundness (20%) Grades
        code_review_results = validation_results_dict.get('code_review_results')
        if code_review_results and code_review_results.get('status') != 'error':
            all_findings = code_review_results.get('static_analysis', [])
            code_style_findings = [f for f in all_findings if not f.get('severity', '').startswith('security')]
            security_findings = [f for f in all_findings if f.get('severity', '').startswith('security')]

            # Code Style Grade Calculation (10%)
            # Penalize based on severity and count
            style_error_penalty = 20 # Higher penalty for errors
            style_warning_penalty = 5 # Lower penalty for warnings
            style_info_penalty = 0 # No penalty for info/convention
            calculated_style_penalty = sum(
                (style_error_penalty if f.get('severity') == 'error' else
                 style_warning_penalty if f.get('severity') == 'warning' else 0)
                for f in code_style_findings
            )
            # Cap penalty at 100%
            style_percentage = max(0, 100 - calculated_style_penalty)
            grades['code_style'] = {
                "percentage": style_percentage,
                "justification": f"Code review found {len(code_style_findings)} style issues. Status: {code_review_results.get('status')}"
            }

            # Security Soundness Grade Calculation (20%)
            # Penalize based on security severity
            sec_high_penalty = 100 # Any high security issue makes grade 0
            sec_medium_penalty = 25
            sec_low_penalty = 5
            calculated_security_penalty = sum(
                (sec_high_penalty if f.get('severity') == 'security_high' else
                 sec_medium_penalty if f.get('severity') == 'security_medium' else
                 sec_low_penalty if f.get('severity') == 'security_low' else 0)
                for f in security_findings
            )
            # Cap penalty at 100%
            security_percentage = max(0, 100 - calculated_security_penalty)
            grades['security_soundness'] = {
                "percentage": security_percentage,
                "justification": f"Security scan found {len(security_findings)} security findings."
            }

        elif code_review_results and code_review_results.get('status') == 'error':
            error_justification = f"Code review/security execution error: {code_review_results.get('message', 'Unknown error')}" # Use message field
            grades['code_style'] = {
                "percentage": 0,
                "justification": error_justification
            }
            grades['security_soundness'] = {
                "percentage": 0,
                "justification": error_justification
            }

        # Ethical Policy Compliance Grade (20%)
        ethical_results = validation_results_dict.get('ethical_analysis_results')
        if ethical_results and ethical_results.get('overall_status') != 'error':
            percentage = 100 if ethical_results.get('overall_status') == 'approved' else 0
            justification = f"Ethical analysis status: {ethical_results.get('overall_status')}. Policy: {ethical_results.get('policy_name', 'N/A')}"
            if ethical_results.get('overall_status') == 'rejected':
                # List specific violation types if available
                violation_details = [f"{k}: {v.get('details', 'N/A')}" for k, v in ethical_results.items() if isinstance(v, dict) and v.get('status') == 'violation']
                justification += f". Violations: {'; '.join(violation_details)}"
            elif ethical_results.get('overall_status') == 'skipped':
                percentage = 0
                justification = f"Ethical analysis skipped: {ethical_results.get('message', 'Unknown reason')}"

            grades['ethical_policy'] = {
                "percentage": percentage,
                "justification": justification
            }
        elif ethical_results and ethical_results.get('overall_status') == 'error':
            grades['ethical_policy'] = {
                "percentage": 0,
                "justification": f"Ethical analysis execution error: {ethical_results.get('message', 'Unknown error')}"
            }

        # Non-Regression Grade (20%) - Placeholder based on Test Success
        # This is a simplification. Real non-regression needs specific tests.
        grades['non_regression'] = {
            "percentage": grades['test_success']['percentage'], # Link directly to test success for now
            "justification": "Non-regression testing is a placeholder. Graded based on Test Success percentage."
        }

        # Calculate Overall Percentage Grade
        # Ensure weights sum to 1.0
        weights = {
            "non_regression": 0.20,
            "test_success": 0.30,
            "code_style": 0.10,
            "ethical_policy": 0.20,
            "security_soundness": 0.20
        }
        total_weight = sum(weights.values())
        if total_weight != 1.0:
             logger.warning(f"Grade weights do not sum to 1.0 (sum={total_weight}). Overall grade may be skewed.")

        overall_percentage = sum(grades[dimension]['percentage'] * weights.get(dimension, 0) for dimension in weights)

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
        if not isinstance(grade_report_json, str):
             logger.error(f"Invalid input type for grade_report_json: {type(grade_report_json)}")
             return {
                 "recommended_action": "Manual Review Required",
                 "justification": "Invalid input for Grade Report evaluation."
             }
        try:
            report_data = json.loads(grade_report_json)
        except json.JSONDecodeError as e:
            logger.error(f"Failed to parse Grade Report JSON: {e}", exc_info=True)
            return {
                "recommended_action": "Manual Review Required",
                "justification": f"Failed to parse Grade Report JSON: {e}"
            }

        grades = report_data.get('grades', {})
        validation_results = report_data.get('validation_results', {})

        overall_percentage_grade = grades.get('overall_percentage_grade', 0)
        test_results = validation_results.get('tests', {})
        code_review_results = validation_results.get('code_review', {})
        ethical_analysis_results = validation_results.get('ethical_analysis', {})

        logger.info(f"Grade Report Metrics: Overall Grade={overall_percentage_grade}%, Test Status={test_results.get('status')}, Ethical Status={ethical_analysis_results.get('overall_status')}, Code Review Status={code_review_results.get('status')}")

        recommended_action = "Manual Review Required" # Default action
        justification = "Evaluation criteria not met or unhandled scenario."

        # Prioritize critical blockers
        if ethical_analysis_results.get('overall_status') == 'rejected':
            recommended_action = "Blocked"
            justification = "Ethical analysis rejected the code."
        elif code_review_results.get('static_analysis') and any(f.get('severity') == 'security_high' for f in code_review_results.get('static_analysis', [])):
            recommended_action = "Blocked"
            justification = "High-risk security findings detected."
        elif test_results.get('status') == 'error' or code_review_results.get('status') == 'error' or ethical_analysis_results.get('overall_status') == 'error':
             recommended_action = "Manual Review Required"
             justification = "Validation tool execution error."
        # Then check for success
        elif overall_percentage_grade == 100:
            recommended_action = "Completed"
            justification = "Overall grade is 100%."
        # Then check for issues that trigger automated remediation (Style, Ethical Transparency)
        # Use the dedicated check method here for consistency
        elif self._check_if_remediation_needed(grade_report_json)[0]: # [0] gets the boolean result
             recommended_action = "Regenerate Code"
             remediation_type = self._check_if_remediation_needed(grade_report_json)[1] # [1] gets the type
             justification = f"Automated remediation triggered for {remediation_type} issues."
        # Then check for other issues that might require regeneration (e.g., test failures)
        elif test_results.get('status') == 'failed':
            recommended_action = "Regenerate Code"
            justification = "Automated tests failed."
        # If grade is below 100 but no specific remediation/test failure trigger, consider regeneration threshold
        elif overall_percentage_grade >= 80: # Example threshold for regeneration
            recommended_action = "Regenerate Code"
            justification = f"Overall grade ({overall_percentage_grade}%) is below 100%, suggesting improvements are needed."
        # If grade is low and no specific trigger, might need manual review
        else: # overall_percentage_grade < 80
            recommended_action = "Manual Review Required"
            justification = f"Overall grade ({overall_percentage_grade}%) is low and requires manual review."


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
        # Ensure inputs are valid
        if not isinstance(roadmap_path, str) or roadmap_path == "":
             logger.error(f"Invalid roadmap_path provided for writing: {roadmap_path}")
             return False
        if not isinstance(new_content, dict):
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Content is not a dictionary.")
            return False
        if 'tasks' not in new_content:
            logger.error(f"Invalid content provided for roadmap file {roadmap_path}: Missing 'tasks' key.")
            return False

        resolved_filepath = self.context.get_full_path(roadmap_path)
        if resolved_filepath is None:
            # This case should ideally be caught by context.get_full_path logging
            logger.error(f"Security alert: Path traversal attempt detected or path could not be resolved for roadmap file: {roadmap_path}")
            return False

        resolved_filepath_obj = Path(resolved_filepath)
        roadmap_dir = resolved_filepath_obj.parent
        # Use a more robust temporary file naming convention
        temp_filename = f"{resolved_filepath_obj.name}.{uuid.uuid4()}.tmp"
        temp_filepath = roadmap_dir / temp_filename

        # Clean up any potential leftover temporary file from a previous failed attempt
        if temp_filepath.exists():
            try:
                os.remove(temp_filepath)
                logger.debug(f"Cleaned up leftover temporary file: {temp_filepath}")
            except Exception as cleanup_e:
                logger.warning(f"Failed to clean up leftover temporary file {temp_filepath}: {cleanup_e}")


        try:
            # Write to the temporary file
            with open(temp_filepath, 'w', encoding='utf-8') as f: # Specify encoding
                json.dump(new_content, f, indent=2)

            # Atomically replace the original file with the temporary file
            os.replace(temp_filepath, resolved_filepath)

            logger.info(f"Successfully wrote updated roadmap to {roadmap_path}")
            return True

        except (IOError, OSError, PermissionError, json.JSONDecodeError) as e:
            logger.error(f"Error writing roadmap file {roadmap_path}: {e}", exc_info=True)
            # Attempt to clean up the temporary file in case of error
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after error: {temp_filepath}")
                except Exception as cleanup_e:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after error: {cleanup_e}")
            return False
        except Exception as e:
            logger.error(f"Unexpected error during roadmap file write {roadmap_path}: {e}", exc_info=True)
            # Attempt to clean up the temporary file in case of error
            if temp_filepath.exists():
                try:
                    os.remove(temp_filepath)
                    logger.debug(f"Cleaned up temporary file after unexpected error: {temp_filepath}")
                except Exception as cleanup_e:
                    logger.warning(f"Failed to clean up temporary file {temp_filepath} after unexpected error: {cleanup_e}")
            return False # Return False on generic exception