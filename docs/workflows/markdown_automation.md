# Markdown-Only Automation Workflow for Metamorphic Genesis Ecosystem (Dual LLM)

**Note:** The current workflow involves manually copying prompts to a Coder LLM and pasting the results back. The *intended future workflow* is to automate this interaction, allowing the Driver LLM to directly invoke the Coder LLM.  **This document describes the workflow as it will be after Phase 1.5 Stage 3 is complete, achieving a fully automated Driver LLM loop.**  *Currently, Phase 1.5 Stage 2 is in progress, and some steps still require manual execution.*

This document describes the "Markdown-Only Automation" workflow for developing the Metamorphic Genesis Ecosystem, leveraging a dual-LLM architecture. This workflow uses specially crafted prompts and augmented `.md` documentation files (ROADMAP.md, CONTRIBUTING.md) to guide an orchestrator (Driver LLM) to autonomously drive development tasks, relying on a secondary model (Coder LLM) to generate code snippets. It enforces a strong emphasis on user oversight and security.

## Overview of the Workflow

The "Markdown-Only Automation" workflow streamlines development by enabling a **Driver LLM** to:

1.  **Identify and select the next development task** from the project's `ROADMAP.json` file.  The `ROADMAP.md` file is now automatically generated *from* `ROADMAP.json`.
2.  **Generate a high-level solution plan** for the selected task.
3.  **Generate precise code generation prompts** for the **Coder LLM.** *In Stage 3, this step will be fully automated. The Driver LLM will directly communicate with the Coder LLM.*
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
    * Ensure you check if the file will be overwriting code. Before writing all files that should be created or replaced, verify with the user if this step is correct.

**Future Enhancement (Phase 1.5 Stage 3):** *Steps 3-6 are currently implemented as instructions for the user to manually copy prompts to a Coder LLM and use the `write_file` tool.  The focus of Phase 1.5 Stage 3 is to fully automate these steps. The Driver LLM will be enhanced to directly invoke the Coder LLM and the `write_file` tool programmatically, removing the need for manual copy-pasting and tool execution. This will enable a truly autonomous, iterative development loop driven by the Driver LLM.*

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
        *   A placeholder section for the Coder LLM's output (e.g., "Coder LLM Output 1: \n\n [PASTE CODER LLM OUTPUT HERE] \n\n").
        *   After pasting the output of the coder LLM, review it to be sure the changes were made according to the requirements. If not, output new instructions for the coder, and a new section for the pasted code.
    *   The complete, ready-to-implement "User Actionable Steps".
    *   The list of actions the AI took for you to verify and run.
    *   The name and source of all files that will be written by calling the `write_file` tool.
    *   The complete "Grade Report" for your *expected* solution. Make it clear that this grade is provisional.
    *   "Updated ROADMAP.md Content": Include the *full text content* of the updated `ROADMAP.md` file, incorporating the task completion marking and roadmap evolution.  Note that this file is now generated automatically, so the provided content should be a reflection of the changes made in `ROADMAP.json`.
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

**Field Descriptions:**

*   `"phase"`: The name of the development phase.
*   `"phase_goal"`: A brief description of the phase's objective.
*   `"success_metrics"`: A list of metrics to measure the phase's success.
*   `"tasks"`: An array of tasks within the phase. Each task is a JSON object with the following keys:
    *   `"task_id"`: A unique identifier for the task. This should be a simple string (e.g., "task_2_3").
    *   `"priority"`: Indicates the importance of the task. Allowed values: `"High"`, `"Medium"`, or `"Low"`.
    *   `"task_name"`: A concise description of the task (under 150 characters).
    *   `"description"`: A detailed description of the task.
    *   `"status"`: Indicates the current state of the task. Allowed values: `"Not Started"`, `"In Progress"`, `"Completed"`, or `"Blocked"`.
* `"next_phase_actions"`:A list of actions to take before transitioning to the next phase.
* `"current_focus"`:A concise description of the team's current work tasks.

**Important Notes:**

*   Use the specified JSON formatting.
*   Task names should be relatively short to avoid parsing issues.

## CLI Integration and Execution

The Markdown-Only Automation Workflow can be executed via the command-line interface (CLI) provided in `src/cli/main.py`.  This CLI allows you to run the WorkflowDriver and initiate the task selection process.

**Basic CLI Usage:**

To run the workflow driver, navigate to the project root directory in your terminal and execute the following command:

```bash
python src/cli/main.py
```

This command will execute the `cli_entry_point()` function in `src/cli/main.py`. By default, it will:

*   Load the roadmap from `ROADMAP.json` in the project root.
*   Use the default output directory `./output`.
*   Select the next task with "Not Started" status from the loaded roadmap.
*   Print information about the selected task (or indicate if no tasks are available).

**CLI Arguments:**

The CLI supports the following arguments to customize its behavior:

*   `--roadmap <path>`: Specifies the path to the `ROADMAP.json` file.  This allows you to use a roadmap file located elsewhere or with a different name.
    *   **Example:** To run the CLI with a roadmap file located at `path/to/my_roadmap.json`, use:
        ```bash
        python src/cli/main.py --roadmap path/to/my_roadmap.json
        ```

*   `--output-dir <path>`: Specifies the path to the output directory where generated files (in future automated steps) would be written. Defaults to `./output` in the project root.
    *   **Example:** To run the CLI and specify `my_output_directory` as the output directory, use:
        ```bash
        python src/cli/main.py --output-dir my_output_directory
        ```

**Combining Arguments:** You can use both arguments together:

```bash
python src/cli/main.py --roadmap path/to/my_roadmap.json --output-dir my_output_directory
```

**Example CLI Execution:**

1.  **Open your terminal** and navigate to the root directory of the `metamorphic-core` project.
2.  **Run the basic command:**

    ```bash
    python src/cli/main.py
    ```

    This will execute the workflow driver with default settings. You should see output similar to:

    ```text
    Using roadmap: /path/to/metamorphic-core/ROADMAP.json
    Using output directory: /path/to/metamorphic-core/output
    Next task selected: ID=task_3_1a, Name=Review Phase 1.5 Stage 2 (Initial Implementation)
    ```

    *If no tasks with "Not Started" status are found, you will see:*

    ```text
    Using roadmap: /path/to/metamorphic-core/ROADMAP.json
    Using output directory: /path/to/metamorphic-core/output
    No tasks available in 'Not Started' status.
    ```

3.  **Experiment with arguments:** Try running the CLI with different roadmap and output directory arguments to see how it changes the behavior:

    ```bash
    python src/cli/main.py --roadmap custom_roadmap.json --output-dir custom_output_dir
    ```

    *Ensure that `custom_roadmap.json` exists (or create a dummy one for testing) and `custom_output_dir` is a valid directory path.*

**Troubleshooting CLI Issues:**

If you encounter issues running the CLI, check the following:

*   **"ROADMAP.json file not found" error:**
    *   **Verify the path:** Ensure that the `ROADMAP.json` file exists at the default location (project root) or the path specified by the `--roadmap` argument is correct.
    *   **File existence:** Double-check that the `ROADMAP.json` file has not been accidentally deleted or moved.

*   **"Output directory not found" error:**
    *   **Verify the path:** Ensure that the output directory path specified by the `--output-dir` argument is correct and that the directory exists.
    *   **Create directory:** If you intend to use a new output directory, make sure to create it manually before running the CLI, or use a path to an existing directory.

*   **"Argument parsing errors" or unexpected behavior:**
    *   **Check command syntax:** Review the CLI command you are using for any typos or incorrect argument names.
    *   **Refer to help message:** Run `python src/cli/main.py --help` to display the CLI help message and verify the correct syntax and available arguments.
    *   **Environment setup:** Ensure you are running the command from the project root directory and that your Python environment is correctly set up (virtual environment activated if used).

## Ready-to-Use "Ideal" Self-Driving Prompt

You are an AI development assistant working on the Metamorphic Software Genesis Ecosystem. Your goal is to autonomously drive the development of the project by following the instructions in docs/workflows/markdown_automation.md. Adhere to the Iterative Grading Process. Pay close attention to writing code that meets ethical standards. Before writing any files, and doing any action, be sure to read and understand them and verify the content is correct and ethical. Never write anything with overwriting files unless it's required.

**IMPORTANT CONTEXT FOR THIS DEVELOPMENT ITERATION:**

    You are currently assisting with the *development* of Phase 1.5 Stage 2. Therefore, you CANNOT directly use any of the following Stage 2 features:
    - the `write_file` tool (you must generate instructions for a *human* to write files)
    - Automated task selection (you MUST select a Task ID from the ROADMAP.json)
    - CLI Integration/Execution (you cannot *execute* commands directly - generate User Actionable Steps for human execution)
    - Automated "WorkflowDriver" Loop/Execution (you must generate solutions for *one task at a time* and wait for human confirmation before proceeding)

You MUST select a Task ID from the ROADMAP.json file to work on, and explicitly state the Task ID you are selecting

1.  Understand the project structure and goals by reading the following documentation:
    *   Full High-Level Specification: [PASTE THE FULL CONTENT OF SPECIFICATION.md HERE]
    *   Development Roadmap: [PASTE THE FULL CONTENT OF ROADMAP.md HERE] *NOTE: Roadmap is autogenerated from ROADMAP.json, so paste the ROADMAP.json content here instead*
    *   Contribution Guidelines: [PASTE THE FULL CONTENT OF CONTRIBUTING.md HERE]
    *   Automation Workflow: [PASTE THE FULL CONTENT OF docs/workflows/markdown_automation.md HERE]
    *   Competitive Landscape: [PASTE THE FULL CONTENT OF COMPETITIVE_LANDSCAPE.md HERE]

2.  Execute the steps described in docs/workflows/markdown_automation.md.
    *   Load the full content of all markdown files.
    *   **Explicitly state the Task ID you are working on**
    *   Identify and select the next development task from ROADMAP.json.
    *   Before generating any code, identify potential conflicts with existing code. Provide a list of files that may be affected and describe the potential conflicts.
        *   Include the output of the `list_files` command to verify file paths.
    *   Generate a high-level solution plan.
    *   For each code modification, design comprehensive tests, predict the expected test outcomes (pass/fail), and justify your test choices to cover edge cases and potential security vulnerabilities.
        *   After pasting the initial test output, assess how the generated tests improve code coverage from the `CodeReviewAgent`'s perspective (Flake8).
    *   Generate precise code generation prompts for the Coder LLM. Ensure generated code follows PEP 8 style guidelines and explain how each line adheres to these guidelines.
    *   Generate precise code generation prompts for the Coder LLM. When generating code, implement sanitization and code injection techniques to address potential vulnerabilities. Then, explain how this was used for the security vulnerability
        *   Output your testing methodology for vulnerability concerns, and how you test.
        *   Output your testing methodology for vulnerability concerns, and how you test.
    *   Generate a numbered list of User Actionable Steps, formatted as a Markdown checklist.
    *   Self-Critique and Revise the generated outputs (Solution Plan, Coder LLM Prompts, User Actionable Steps).
    *   Perform a self-assessment and grade the proposed solution using the Iterative Grading Process from CONTRIBUTING.md.

3.  Ensure all generated code adheres to the project's ethical policies and guidelines, using policy_bias_risk_strict.json and ethical_policy_schema.json as references. Justify how the code adheres to the specified thresholds and enforcement levels in ethical_policy_schema.json. Use sanitization and code injections to ensure the code follows secure requirements
    *   Make sure that no keyword identified in that file's "keywords" list (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code.

Remember to follow these guidelines to the greatest extent possible. Await human confirmation before commencing any additional tasks or stages.

## ROADMAP.json Format

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
    *   `"task_id"`:  A unique string identifying the task (e.g., `"task_2_3"`).  This *cannot* contain `/` or `..` sequences (to prevent path traversal vulnerabilities).
    *   `"priority"`:  A string indicating the task's priority. Allowed values: `"High"`, `"Medium"`, or `"Low"`.
    *   `"task_name"`:  A concise string description of the task (150 characters or less).
    *   `"status"`: A string indicating the task's current status. Allowed values: `"Not Started"`, `"In Progress"`, `"Completed"`, or `"Blocked"`.
    *   `"description"`: A string providing a more detailed description of the task.  HTML characters in this field will be automatically escaped to prevent XSS vulnerabilities.
*   The `"phase"`, `"phase_goal"`, `"success_metrics"`, `"next_phase_actions"`, and `"current_focus"` fields are also required at the top level.

**Validation:**

*   Before submitting a pull request that modifies `ROADMAP.json`, please ensure that your changes are valid JSON and conform to the structure described above. You can use a JSON validator (many are available online) to check the syntax. The CI build includes similar validation, but it's always best to catch errors early.
*   After modifying `ROADMAP.json`, run `python scripts/generate_roadmap_md.py` locally to generate the `ROADMAP.md` file and visually inspect the output for any formatting issues or errors.

## File Format Considerations
*   `ROADMAP.md` - see `docs/workflows/markdown_automation.md` for file format and formatting requirements. **The `ROADMAP.md` file is now automatically generated from `ROADMAP.json`.  DO NOT EDIT THIS FILE DIRECTLY!** All roadmap contributions must be made by editing `ROADMAP.json`. See `docs/workflows/markdown_automation.md` for details on the `ROADMAP.json` format and how to contribute to the roadmap.