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
+       **"You must include the complete Grade Report in this response, in the proper section. The grade report needs to be included as a JSON object, to allow for easy readability."**
+        **"The Grade Report should be copied, pasted, and then converted to JSON, to allow for more accurate review."**
     *   "Updated ROADMAP.md Content": Include the *full text content* of the updated `ROADMAP.md` file, incorporating the task completion marking and roadmap evolution.
     *   **Context Files Used:** Explicitly list the Markdown files that you (the Driver LLM) used as context to perform this task. This should typically include, but is not limited to, `ROADMAP.md` and `CONTRIBUTING.md`. List each file on a new line using Markdown list syntax (e.g., `* ROADMAP.md`).
     *   **End your response with the following choices:**
+        ***IMPORTANT:*** *Because your goal is to achieve a 100% Overall Percentage Grade in the Iterative Grading Process, you CANNOT choose "A: Confirm" in the current workflow.  You must address all feedback until a 100% grade is achieved.*
+        *The weights reflect the importance of each dimension. For example, Test Success receives the highest weighting, and code style gets the lowest weighting*
         *   **(A) Confirm:** If the proposed changes are satisfactory and tests are passing (or there are no tests), implement the changes and proceed to the next task. **Example: `A: All tests passed. Implementing changes and moving on.`**
         *   **(B) Test(s) Not Passing:** If the proposed changes are implemented but tests are failing, provide detailed information about the failing tests. (Copy and paste the test output). **Example: `B: Test tests/test_api_mvp_endpoint.py::test_analyze_ethical_endpoint_no_code_integration failed with AssertionError: assert response.status_code == 200`**
         *   **(C) Ask Question:** If you want to ask the LLM a question about its approach or the proposed solution *before* implementing any changes. (State your question clearly). **Example: `D: Could you explain why you chose to use the 'dataclasses' module in this context?`**
@@ -98,9 +99,9 @@
         *   **(F) Regenerate:** If you want the current task regenerated, include a very short prompt to explain why. **Example: `F: This code could be greatly simplified.`**
 
         **Important: Ensure all generated code adheres to the project's ethical policies and guidelines. For example, if the "BiasRisk" threshold is 0.1, make sure that no keyword identified in `policies/policy_bias_risk_strict.json` (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code.**
-+        **"You must include the complete Grade Report in this response, in the proper section. The grade report needs to be included as a JSON object, to allow for easy readability."**
         **Your response MUST begin with one of the letters above (A, B, C, D, E, or F) followed by a colon and a space, then your message.** For example: "B: Test test_my_function failed with assertion error..."
-+        **"The Grade Report should be copied, pasted, and then converted to JSON, to allow for more accurate review."**
+
+
         **If your response DOES NOT begin with A, B, C, D, E, or F, or if you did not include all of the requested details, ask me to resend the full, un-truncated message.**
 
         (Waiting for user confirmation to implement changes and proceed to the next task)
