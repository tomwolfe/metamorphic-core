 Markdown-Only Automation Workflow for Metamorphic Genesis Ecosystem (Dual LLM)

**Note:** This document describes the "Markdown-Only Automation" workflow as it functions *after* the successful completion of Phase 1.5 Stage 3 and the implementation of Phase 1.6. **Phase 1.5 Stage 3 is now complete, achieving a fully automated Driver LLM loop for task selection, planning, agent invocation, and file management.** **Phase 1.6 is now complete, automating the initial prompt submission via CLI/API, the execution of validation steps (tests, code review, security), the parsing of the Grade Report, and the updating of the roadmap status.** The workflow is now largely autonomous, initiated by a single CLI command.

This document describes the "Markdown-Only Automation" workflow for developing the Metamorphic Genesis Ecosystem, leveraging a dual-LLM architecture. This workflow uses specially crafted prompts and augmented `.md` documentation files (ROADMAP.md, CONTRIBUTING.md) to guide an orchestrator (Driver LLM) to autonomously drive development tasks, relying on a secondary model (Coder LLM) to generate code snippets. It enforces a strong emphasis on user oversight and security.

## Overview of the Workflow (Post-Phase 1.6)

The "Markdown-Only Automation" workflow, as implemented through Phase 1.5 and Phase 1.6, enables a **Driver LLM** to autonomously drive development tasks from initiation through validation and roadmap update. The workflow steps executed autonomously by the Driver LLM **(orchestrated via the `/genesis/drive_workflow` API endpoint, triggered by the CLI)** are:

1.  **Identify and select the next development task** from the project's `ROADMAP.json` file **(loaded using the path provided to the API endpoint)**. The `ROADMAP.md` file is now automatically generated *from* `ROADMAP.json`.
2.  Generate a high-level solution plan for the selected task.
3.  Iterate through the solution plan steps.
4.  Invoke necessary agents and tools based on the plan step description. This includes automatically invoking the Coder LLM for code generation steps and automatically using the `write_file` and `list_files` tools for file management steps.
5.  Generate precise code generation prompts for the **Coder LLM.** The Driver LLM automatically invokes the Coder LLM with these prompts when needed.
6.  Generate a numbered list of "User Actionable Steps" for the user to perform *after* the autonomous iteration is complete (e.g., reviewing changes, providing feedback if needed). Format these steps as a Markdown checklist to enhance readability and trackability. Each step should start with a numbered list item, followed by a Markdown checklist syntax ` - [ ] ` and then the step description. For example:

    ```markdown
    1.  - [ ] Step 1 description goes here.
    2.  - [ ] Step 2 description goes here.
    3.  - [ ] ... and so on.
    ```

    The user will execute these steps and verify the results.
7.  Call the `list_files` tool, to confirm all files that the write_file tool will modify. Write a description to the user for what file will be written.
8.  Call the `write_file` tool, to write all code to file.
    * Ensure you check if the file will be overwriting code. Before writing all files that should be created or replaced, verify with the user if this step is correct. The Driver LLM now automatically invokes the `write_file` tool.
9.  Self-Critique and Revise Output: Before proceeding to self-assessment, the Driver LLM reviews its generated output from the autonomous iteration (steps 1-8). Specifically:

    *   Solution Plan Review: Is the solution plan logical and comprehensive? Does it clearly address the selected task? Are there any missing steps or potential issues?
    *   Coder LLM Prompt Review: Are the generated prompts for the Coder LLM clear, concise, and well-contextualized? Do they provide sufficient information for the Coder LLM to generate the correct code? Are the instructions unambiguous?
    *   User Actionable Steps Review: Are the User Actionable Steps complete, clear, and easy to follow for a developer? Are there any missing steps or unclear instructions?
    *   Revision (If Necessary): If, during its self-critique, the Driver identifies any weaknesses or areas for improvement in the solution plan, Coder LLM prompts, or User Actionable Steps, it revises them immediately. It iterates on these outputs to improve their clarity, completeness, and quality before proceeding to self-assessment.
10. Automatically execute validation steps: The Driver automatically triggers execution of tests (e.g., `pytest`), code review (`CodeReviewAgent`), and security checks (`SecurityAgent`) on the generated/modified code. It captures the results (pass/fail, issues found).
11. Perform a self-assessment and grade the proposed solution using the metrics and guidelines defined in the "Iterative Grading Process" section of CONTRIBUTING.md and the "LLM INSTRUCTION: CONTRIBUTION REVIEW GUIDANCE" block in CONTRIBUTING.md. Generate a structured "Grade Report" in JSON format, including results from the automated validation steps.
12. Automatically parse the Grade Report and determine the outcome: The Driver parses the JSON Grade Report and evaluates the results (e.g., test pass rate, severity of issues, overall grade). Based on predefined criteria, it determines if the task iteration was successful, requires regeneration, or needs manual intervention.
13. Automatically update the task status in `ROADMAP.json`: Based on the outcome determined in the previous step, the Driver updates the status of the current task in `ROADMAP.json` (e.g., sets status to "Completed" if successful, "Blocked" if critical issues found).

**Primary Remaining Manual Step:** The user must initiate the workflow by running the CLI command (`python src/cli/main.py`) and review the outputs and logs after the autonomous iteration is complete.

14. Output the following in markdown format:

    *   The selected task name and description.
    *   The complete high-level solution plan.
    *   **For each code modification step:**
        *   A clear label for the code generation prompt (e.g., "Coder LLM Prompt 1: Modify `calculate_area` function").
        *   The complete code generation prompt for the Coder LLM.
        *   The Coder LLM's output (this is now automated).
        *   After the automated output of the coder LLM is received, review it to be sure the changes were made according to the requirements. If not, output new instructions for the coder, and a new section for the pasted code.
    *   The complete, ready-to-implement "User Actionable Steps".
    *   The list of actions the AI took for you to verify and run (this now includes automated validation execution).
    *   The name and source of all files that were written by calling the `write_file` tool.
    *   The complete "Grade Report" (now generated and parsed automatically).
    *   "Updated ROADMAP.json Status": Indicate the new status of the task in `ROADMAP.json` (which was updated automatically).
    *   **Context Files Used:** Explicitly list the Markdown files that you (the Driver LLM) used as context to perform this task. This should typically include, but is not limited to, `ROADMAP.md` and `CONTRIBUTING.md`. List each file on a new line using Markdown list syntax (e.g., `* ROADMAP.md`).
    *   **End your response with the following choices:**

        *   **(A) Confirm:** If the autonomous iteration was successful (tests passed, grade is high, roadmap status updated correctly), confirm the outcome. **Example: `A: Autonomous iteration successful. Task status updated in ROADMAP.json.`**
        *   **(B) Review Required:** If the autonomous iteration resulted in issues requiring manual review or intervention (e.g., task marked 'Blocked', critical errors logged). **Example: `B: Task marked as Blocked in ROADMAP.json due to critical security issues. Manual review required.`**
        *   **(C) Ask Question:** If you want to ask the LLM a question about its approach or the proposed solution *before* implementing any changes (less common now with full automation, but still possible for complex scenarios). (State your question clearly). **Example: `C: Could you explain the rationale behind the generated solution plan?`**
        *   **(D) Regenerate:** If you want the current task iteration regenerated, include a very short prompt to explain why (e.g., "Code did not meet requirements"). **Example: `D: Generated code failed automated tests.`**

        **Important: Before writing to any file, double check, using list files that the file path doesn't exist. Ensure all generated code adheres to the project's ethical policies and guidelines. For example, if the "BiasRisk" threshold is 0.1, make sure that no keyword identified in `policies/policy_bias_risk_strict.json` (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code.**

        **Your response MUST begin with one of the letters above (A, B, C, or D) followed by a colon and a space, then your message.** For example: "B: Task marked as Blocked..."

## ROADMAP.json Format

To ensure proper parsing and automation, the `ROADMAP.json` file must adhere to a specific format. Each task entry should be structured as follows:

```json
{
    "phase": "Phase Name",
    "phase_goal": "Goal of the Phase",
    "success_metrics": [],
    "tasks": [
        {
            "task_id": "task_1_1",
            "priority": "High",
            "task_name": "Example Task",
            "description": "Details of the task",
            "status": "Not Started"
        }
    ],
    "next_phase_actions": [],
    "current_focus": "🎯 CURRENT FOCUS: [Concise description of current focus]"
}
```

**Field Requirements:**

*   The top-level structure *must* be a JSON object (dictionary).
*   The object *must* contain a `"tasks"` key.
*   The value associated with the `"tasks"` key *must* be a JSON array.
*   Each element in the `"tasks"` array *must* be a JSON object (dictionary) representing a single task.
*   Each task object *must* contain the following keys:
    *   `"task_id"`: A unique string identifying the task (e.g., `"task_2_3"`). This *cannot* contain `/` or `..` sequences (to prevent path traversal vulnerabilities).
    *   `"priority"`: A string indicating the task's priority. Allowed values: `"High"`, `"Medium"`, or `"Low"`.
    *   `"task_name"`: A concise string description of the task (150 characters or less).
    *   `"status"`: A string indicating the task's current status. Allowed values: `"Not Started"`, `"In Progress"`, `"Completed"`, or `"Blocked"`.
    *   `"description"`: A string providing a more detailed description of the task. HTML characters in this field will be automatically escaped to prevent XSS vulnerabilities.
*   The `"phase"`, `"phase_goal"`, `"success_metrics"`, `"next_phase_actions"`, and `"current_focus"` fields are also required at the top level.

**Validation:**

*   Before submitting a pull request that modifies `ROADMAP.json`, please ensure that your changes are valid JSON and conform to the structure described above. You can use a JSON validator (many are available online) to check the syntax. The CI build includes similar validation, but it's always best to catch errors early.
*   After modifying `ROADMAP.json`, run `python scripts/generate_roadmap_md.py` locally to generate the `ROADMAP.md` file and visually inspect the output for any formatting issues or errors.

## File Format Considerations
