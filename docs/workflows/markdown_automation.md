# Markdown-Only Automation Workflow for Metamorphic Genesis Ecosystem (Dual LLM)

**Note:** The current workflow involves manually copying prompts to a Coder LLM and pasting the results back. The *intended future workflow* is to automate this interaction, allowing the Driver LLM to directly invoke the Coder LLM. **This document describes the workflow as it will be after Phase 1.5 Stage 3 is complete, achieving a fully automated Driver LLM loop.** *Currently, Phase 1.5 Stage 2 is in progress, and some steps still require manual execution. Specifically, the Driver LLM now automatically invokes the Coder LLM and the `write_file` tool (as of task_2_9a), but the overall Driver loop (task selection, plan generation, etc.) still requires human prompting and execution of User Actionable Steps.*

This document describes the "Markdown-Only Automation" workflow for developing the Metamorphic Genesis Ecosystem, leveraging a dual-LLM architecture. This workflow uses specially crafted prompts and augmented `.md` documentation files (ROADMAP.md, CONTRIBUTING.md) to guide an orchestrator (Driver LLM) to autonomously drive development tasks, relying on a secondary model (Coder LLM) to generate code snippets. It enforces a strong emphasis on user oversight and security.

## Overview of the Workflow

The "Markdown-Only Automation" workflow streamlines development by enabling a **Driver LLM** to:

1.  **Identify and select the next development task** from the project's `ROADMAP.json` file. The `ROADMAP.md` file is now automatically generated *from* `ROADMAP.json`.
2.  **Generate a high-level solution plan** for the selected task.
3.  **Generate precise code generation prompts** for the **Coder LLM.** **As of Phase 1.5 Stage 2 (task_2_9a), the Driver LLM now automatically invokes the Coder LLM with these prompts.**
4.  **Generate a numbered list of "User Actionable Steps"** to guide the user. Format these steps as a Markdown checklist to enhance readability and trackability. Each step should start with a numbered list item, followed by a Markdown checklist syntax ` - [ ] ` and then the step description. For example:

    ```markdown
    1.  - [ ] Step 1 description goes here.
    2.  - [ ] Step 2 description goes here.
    3.  - [ ] ... and so on.
    ```

    The user will execute these steps and verify the results.
5.  Call the `list_files` tool, to confirm all files that the write_file tool will modify. Write a description to the user for what file will be written.

    *Note*: Before calling the `write_file` tool, the LLM should output the `list_files` and double check that all the changes are made correctly.
6.  Call the `write_file` tool, to write all code to file.
    * Ensure you check if the file will be overwriting code. Before writing all files that should be created or replaced, verify with the user if this step is correct. **As of Phase 1.5 Stage 2 (task_2_9a), the Driver LLM now automatically invokes the `write_file` tool.**

**Future Enhancement (Phase 1.5 Stage 3):** *Steps 3 and 6 (Coder LLM invocation and `write_file` tool execution) are now automated as part of Phase 1.5 Stage 2. The focus of Phase 1.5 Stage 3 is to fully automate the *entire* Driver LLM loop, including automated task selection, solution planning, and execution of the full workflow without requiring manual prompting of the Driver LLM itself. This will enable a truly autonomous, iterative development loop.*

7.  **Self-Critique and Revise Output:** Before proceeding to self-assessment, take a moment to review your generated output from steps 1-6. Specifically:

    *   **Solution Plan Review:** Is the solution plan logical and comprehensive? Does it clearly address the selected task? Are there any missing steps or potential issues?
    *   **Coder LLM Prompt Review:** Are the generated prompts for the Coder LLM clear, concise, and well-contextualized? Do they provide sufficient information for the Coder LLM to generate the correct code? Are the instructions unambiguous?
    *   **User Actionable Steps Review:** Are the User Actionable Steps complete, clear, and easy to follow for a developer? Are there any missing steps or unclear instructions?
    *   **Revision (If Necessary):** If, during your self-critique, you identify any weaknesses or areas for improvement in your solution plan, Coder LLM prompts, or User Actionable Steps, **revise them immediately**. Iterate on these outputs to improve their clarity, completeness, and quality before proceeding to self-assessment.

8.  **Perform a self-assessment and grade your proposed solution** using the metrics and guidelines defined in the "Iterative Grading Process" section of CONTRIBUTING.md and the **<ins>UPDATED</ins>** "LLM INSTRUCTION: CONTRIBUTION REVIEW GUIDANCE" block in CONTRIBUTING.md. Generate a "Grade Report" in markdown format. Remember to include a section for manual feedback, to check security requirements. Since you can't execute code, you must propose what you expect the result to be.

9.  **Output the following in markdown format:**

    *   The selected task name and description.
    *   The complete high-level solution plan.
    *   **For each code modification step:**
        *   A clear label for the code generation prompt (e.g., "Coder LLM Prompt 1: Modify `calculate_area` function").
        *   The complete code generation prompt for the Coder LLM.
        *   A placeholder section for the Coder LLM's output (e.g., "Coder LLM Output 1: \n\n [CODER LLM OUTPUT IS NOW AUTOMATED] \n\n").
        *   After the automated output of the coder LLM is received, review it to be sure the changes were made according to the requirements. If not, output new instructions for the coder, and a new section for the pasted code.
    *   The complete, ready-to-implement "User Actionable Steps".
    *   The list of actions the AI took for you to verify and run.
    *   The name and source of all files that will be written by calling the `write_file` tool.
    *   The complete "Grade Report" for your *expected* solution. Make it clear that this grade is provisional.
    *   "Updated ROADMAP.md Content": Include the *full text content* of the updated `ROADMAP.md` file, incorporating the task completion marking and roadmap evolution. Note that this file is now generated automatically, so the provided content should be a reflection of the changes made in `ROADMAP.md`.
    *   **Context Files Used:** Explicitly list the Markdown files that you (the Driver LLM) used as context to perform this task. This should typically include, but is not limited to, `ROADMAP.md` and `CONTRIBUTING.md`. List each file on a new line using Markdown list syntax (e.g., `* ROADMAP.md`).
    *   **End your response with the following choices:**

        *   **(A) Confirm:** If the proposed changes are satisfactory and tests are passing (or there are no tests), implement the changes and proceed to the next task. **Example: `A: All tests passed. Implementing changes and moving on.`**
        *   **(B) Test(s) Not Passing:** If the proposed changes are implemented but tests are failing, provide detailed information about the failing tests. (Copy and paste the test output). **Example: `B: Test tests/test_api_mvp_endpoint.py::test_analyze_ethical_endpoint_no_code_integration failed with AssertionError: assert response.status_code == 200`**
        *   **(C) Ask Question:** If you want to ask the LLM a question about its approach or the proposed solution *before* implementing any changes. (State your question clearly). **Example: `D: Could you explain why you chose to use the 'dataclasses' module in this context?`**
        *   **(E) Code Issue:** If you have reviewed the code and see an error you want to point out. **Example: `E: It looks like the condition on Line 42 will always evaluate to false.`**
        *   **(F) Regenerate:** If you want the current task regenerated, include a very short prompt to explain why. **Example: `F: This code could be greatly simplified.`**

        **Important: Before writing to any file, double check, using list files that the file path doesn't exist. Ensure all generated code adheres to the project's ethical policies and guidelines. For example, if the "BiasRisk" threshold is 0.1, make sure that no keyword identified in `policies/policy_bias_risk_strict.json` (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code.**

        **Your response MUST begin with one of the letters above (A, B, C, D, E, or F) followed by a colon and a space, then your message.** For example: "B: Test test_my_function failed with assertion error..."

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
*   `ROADMAP.md` - see `docs/workflows/markdown_automation.md` for file format and formatting requirements. **The `ROADMAP.md` file is now automatically generated from `ROADMAP.json`. DO NOT EDIT THIS FILE DIRECTLY!** All roadmap contributions must be made in `ROADMAP.json`. See `docs/workflows/markdown_automation.md` for details on the `ROADMAP.json` format and how to contribute to the roadmap.