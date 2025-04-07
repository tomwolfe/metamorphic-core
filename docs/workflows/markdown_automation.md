# Markdown-Only Automation Workflow for Metamorphic Genesis Ecosystem (Dual LLM)

This document describes the "Markdown-Only Automation" workflow for developing the Metamorphic Software Genesis Ecosystem, leveraging a dual-LLM architecture. This workflow uses specially crafted prompts and augmented `.md` documentation files (ROADMAP.md, CONTRIBUTING.md) to guide an orchestrator (Driver LLM) to autonomously drive development tasks, relying on a secondary model (Coder LLM) to generate code snippets. It enforces a strong emphasis on user oversight and security.

## Overview of the Workflow

The "Markdown-Only Automation" workflow streamlines development by enabling a **Driver LLM** to:

1.  **Identify and select the next development task** from the project's [ROADMAP.md](ROADMAP.md) file.
2.  **Generate a high-level solution plan** for the selected task.
3.  **Generate precise code generation prompts** for the **Coder LLM.**
4.  **Generate a numbered list of "User Actionable Steps"** to guide the user. Format these steps as a Markdown checklist to enhance readability and trackability. Each step should start with a numbered list item, followed by a Markdown checklist syntax ` - [ ] ` and then the step description. For example:

    ```markdown
    1.  - [ ] Step 1 description goes here.
    2.  - [ ] Step 2 description goes here.
    3.  - [ ] ... and so on.
    ```

    The user will execute these steps and verify the results.
5.  Call the `list_files` tool, to confirm all files that the write_file tool will modify. Write a description to the user for what file will be written.
6.  Call the `write_file` tool, to write all code to file.

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
    *   "Updated ROADMAP.md Content": Include the *full text content* of the updated `ROADMAP.md` file, incorporating the task completion marking and roadmap evolution.
    *   **Context Files Used:** Explicitly list the Markdown files that you (the Driver LLM) used as context to perform this task. This should typically include, but is not limited to, `ROADMAP.md` and `CONTRIBUTING.md`. List each file on a new line using Markdown list syntax (e.g., `* ROADMAP.md`).
    *   **End your response with the following choices:**

        *   **(A) Confirm:** If the proposed changes are satisfactory and tests are passing (or there are no tests), implement the changes and proceed to the next task. **Example: `A: All tests passed. Implementing changes and moving on.`**
        *   **(B) Test(s) Not Passing:** If the proposed changes are implemented but tests are failing, provide detailed information about the failing tests. (Copy and paste the test output). **Example: `B: Test tests/test_api_mvp_endpoint.py::test_analyze_ethical_endpoint_no_code_integration failed with AssertionError: assert response.status_code == 200`**
        *   **(C) Ask Question:** If you want to ask the LLM a question about its approach or the proposed solution *before* implementing any changes. (State your question clearly). **Example: `D: Could you explain why you chose to use the 'dataclasses' module in this context?`**
        *   **(E) Code Issue:** If you have reviewed the code and see an error you want to point out. **Example: `E: It looks like the condition on Line 42 will always evaluate to false.`**
        *   **(F) Regenerate:** If you want the current task regenerated, include a very short prompt to explain why. **Example: `F: This code could be greatly simplified.`**

        **Important: Ensure all generated code adheres to the project's ethical policies and guidelines. For example, if the "BiasRisk" threshold is 0.1, make sure that no keyword identified in `policies/policy_bias_risk_strict.json` (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code.**

        **Your response MUST begin with one of the letters above (A, B, C, D, E, or F) followed by a colon and a space, then your message.** For example: "B: Test test_my_function failed with assertion error..."

        **If your response DOES NOT begin with A, B, C, D, E, or F, or if you did not include all of the requested details, ask me to resend the full, un-truncated message.**

        (Waiting for user confirmation to implement changes and proceed to the next task)

10.  After providing the above output, WAIT for my confirmation before proceeding to any further tasks. Do not automatically move to the next task until I explicitly confirm implementation of the current solution AND the ROADMAP.md update. I will respond with one of the following options:

   * **"A: [Optional message if all tests passed, and implementing changes]"**
    *   **"B: [Detailed test output showing failing tests]"**
    *   **"C: [Detailed output of list_files tool]"**
    *   **"D: [Your question to the LLM]"**
    *   **"E: [Describe a code issue you've found]"**
    *   **"F: [Reason for regenerating, e.g., 'Tests are too basic' or 'Code is inefficient']"**

   Your response to my message should depend on the option I choose. Also, ensure all generated code adheres to ethical standards, guided by the `policies/policy_bias_risk_strict.json` example provided. If the "BiasRisk" threshold is 0.1, make sure that no keyword identified in that file's "keywords" list (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code:

    *   If I respond with "A:", proceed to the next task as usual, after updating the ROADMAP.md. If the response was unusually long or had issues with code, summarize the most important aspects.
    *   If I respond with "B:", analyze the provided test output and revise the code to fix the failing tests. Re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".
    *   If I respond with "C:", analyze the current code and create the missing files needed for the correct functioning of the changes. Then present the updated solution, including the list of files, re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".
    *   If I respond with "D:", answer my question clearly and concisely. Do not proceed to the next task after answering. Simply wait for a new prompt from me. If the response from me seems incomplete, ask me to provide the complete message again or re-send just the important data.
    *   If I respond with "E:", analyze the code issue, revise the code to address the issue. Re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".
    *   If I respond with "F:", regenerate the solution from scratch. Incorporate the reason for regeneration into your solution generation process. Re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".

    If my response does NOT begin with A, B, C, D, E or F, output the following error message, then wait for further instructions: "ERROR: Invalid response format. Your response MUST begin with A, B, C, D, E, or F, followed by a colon and a space. If all of the relevant code or data is not provided, please include all of the content in the resent response or a truncated part."

**Example: Creating a New Class "WorkflowDriver" and Method "load_roadmap"**

Suppose you are tasked with creating a new class called `WorkflowDriver` in a new file called `src/core/automation/workflow_driver.py`. This class should have a method, load_roadmap, that will read `ROADMAP.md` and parse it for all outstanding tasks, using regular expressions to pull the required information.

1.  **Break down the task:**

    *   Step 1: Create the basic class structure in `src/core/automation/workflow_driver.py` with `__init__` method and docstrings.
    *   Step 2: Add a method called `load_roadmap` to the `WorkflowDriver` class that reads `ROADMAP.md` and parses the task list. This method should use a regular expression that includes the ID, Title, and Description of all tasks. Consider file safety and loading.
    *   Step 3: Ensure that the `load_roadmap` method contains robust parsing, and consider boundary cases such as blank headers and task descriptions.
    *   Step 4: Add unit tests for the parsing method to verify loading and integrity.

2.  **Tool Utilizations:**

    *   Make sure to use flake8 to review the files, and attempt to use bandit to search for any security issues.

3.  **Model Choices:**

    *   When writing the actual code, consider that DeepSeek can provide a good balance between quality and efficiency, and the most cost-effective model should be chosen if it meets requirements.

4.  **Generate Coder LLM Prompts:**

    *   "Coder LLM Prompt 1: Create a new file `src/core/automation/workflow_driver.py` with the following content:

    ```python
    \"\"\"
    This module provides a WorkflowDriver class for automating tasks.
    \"\"\"

    class WorkflowDriver:
        \"\"\"
        A class for automating tasks defined in the ROADMAP.md.
        \"\"\"

        def __init__(self):
            pass

        def load_roadmap(self, roadmap_path: str):
            \"\"\"
            Loads and parses the ROADMAP.md file.
            \"\"\"
            pass
    ```"
    *   "Coder LLM Prompt 2: Using regex, fill in the content of the method `load_roadmap`. You must use triple quotes to represent an escaped string. For simplicity, ensure that all lines have a length of fewer than 80 characters."

        *  Consider this approach as test-driven development; create the tests first, then have the model iterate it's code to ensure compliance with those tests.