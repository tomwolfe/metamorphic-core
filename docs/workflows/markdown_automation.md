# Markdown-Only Automation Workflow for Metamorphic Genesis Ecosystem (Dual LLM)

This document describes the "Markdown-Only Automation" workflow for developing the Metamorphic Software Genesis Ecosystem, leveraging a dual-LLM architecture. This workflow uses specially crafted prompts and augmented `.md` documentation files (ROADMAP.md, CONTRIBUTING.md) to guide an orchestrator (Driver LLM) to autonomously drive development tasks, relying on a secondary model (Coder LLM) to generate code snippets. It enforces a strong emphasis on user oversight and security.

## Overview of the Workflow

The "Markdown-Only Automation" workflow streamlines development by enabling a **Driver LLM** to:

1.  **Identify and select the next development task** from the project's [ROADMAP.md](ROADMAP.md) file.
2.  **Generate a high-level solution plan** for the selected task.
3.  **Generate precise code generation prompts** for the **Coder LLM.**
4.  **Generate a complete set of "User Actionable Steps"** for the user, to implement and verify the solution (including copying prompts to the Coder LLM and pasting the results back).
5.  **Perform a multi-dimensional self-assessment** of the *expected* solution (based on the plan), using the "Iterative Grading Process" defined in [CONTRIBUTING.md](CONTRIBUTING.md).
6.  **Iteratively revise the solution** (generate new prompts for the Coder LLM) to achieve a satisfactory grade, based on user-provided feedback.
7.  **Wait for user confirmation** before proceeding to the next task, ensuring human oversight at each step.

**LLM Persona Expectations:**

*   **Driver LLM (Orchestrator):**
    *   *Purpose:* To manage development steps, read project documents, and communicate with the Coder LLM.
    *   *Abilities:* This LLM identifies tasks, calls tools, and follows the project instructions.
    *   *Security:* This LLM does not have the ability to write to any file, or execute any code, improving overall security.
    *   *Instructions:* The user must provide the list of available files in the repository.

*   **Coder LLM (Code Specialist):**
    *   *Purpose:* To generate code snippets.
    *   *Instructions:* The coder must return *only* a code block within a markdown structure. It must follow all provided instructions.
    *   *Output Only:* There is no tool call functionality.

This workflow is driven by a single, comprehensive prompt (detailed below) and relies heavily on **"LLM INSTRUCTION" blocks embedded within the `.md` documentation files** (ROADMAP.md and CONTRIBUTING.md). The user acts as an intermediary, executing the actions and copying feedback between the LLMs.

## The "Ideal Self-Driving Prompt"

Here is the complete, ready-to-use "Ideal Self-Driving Prompt" for this workflow, designed for the *Driver LLM*:

<div style="background-color:#e0f7fa; border: 2px solid #80deea; padding: 15px; margin-top: 10px; margin-bottom: 20px;">
<p style="font-family: monospace; font-size: 14px; line-height: 1.4;">

```
I have this codebase:

Here is the source list:
[INSERT FILE LIST - use list_files()]

I am providing these *.md files which drive the development process for this project:

[INSERT FULL CONTENT OF ROADMAP.MD FILE HERE]

[INSERT FULL CONTENT OF CONTRIBUTING.MD FILE HERE]

Please act as an autonomous development agent (Driver LLM) for this project. You will drive development and will communicate with an isolated LLM to handle code requests.

Your task is to:

1. **Identify the next smallest, highest priority development task** from ROADMAP.md, following the "LLM INSTRUCTION: TASK SELECTION" block in that file and using the "Priority" field to determine the order.

2. **Generate a high-level solution plan** for this task. This plan should identify the files to modify, the general coding approach, and any dependencies.

3. **For each code modification step in the plan, generate a *specific, limited-context prompt* for the Coder LLM.** These prompts should be:
    * Concise: Focus on a single, well-defined coding task.
    * Contextual: Include only the *necessary* code snippets (function signature, surrounding code block).
    * Instruction-Oriented: Provide explicit instructions on *what* code to generate or modify. The Coder LLM should only follow instructions, not create them.
    * Ensure all code to be generated adheres to project's ethical policies and guidelines, as defined in `CONTRIBUTING.md`.

4. **Generate a numbered list of "User Actionable Steps"** to guide the user. The user will execute these steps and verify the results.

5. Call the `list_files` tool, to confirm all files that the write_file tool will modify. Write a description to the user for what file will be written.

6. Call the `write_file` tool, to write all code to file.

7.  **Perform a self-assessment and grade your proposed solution** using the metrics and guidelines defined in the "Iterative Grading Process" section of CONTRIBUTING.md and the "LLM INSTRUCTION: CONTRIBUTION REVIEW GUIDANCE" block in CONTRIBUTING.md. Generate a "Grade Report" in markdown format. Remember to include a section for manual feedback, to check security requirements. Since you can't execute code, you must propose what you expect the result to be.

8. **Output the following in markdown format:**

    *   The selected task name and description.
    *   The complete high-level solution plan.
    *   **For each code modification step:**
        *   A clear label for the code generation prompt (e.g., "Coder LLM Prompt 1: Modify `calculate_area` function").
        *   The complete code generation prompt for the Coder LLM.
        *   A placeholder section for the Coder LLM's output (e.g., "Coder LLM Output 1: \n\n [PASTE CODER LLM OUTPUT HERE] \n\n").
        *   After pasting the output of the coder LLM, review it to be sure the changes were made according to the requirements. If not, output new instructions for the coder, and a new section for the pasted code.
    *   The complete, ready-to-implement "User Actionable Steps".
    * The list of actions the AI took for you to verify and run.
    *   The name and source of all files that will be written by calling the `write_file` tool.
    *   The complete "Grade Report" for your *expected* solution. Make it clear that this grade is provisional.
    *   "Updated ROADMAP.md Content": Include the *full text content* of the updated `ROADMAP.md` file, incorporating the task completion marking and roadmap evolution.
        **- Provide all data to the user so they can follow each change.**

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

9.  After providing the above output, WAIT for my confirmation before proceeding to any further tasks. Do not automatically move to the next task until I explicitly confirm implementation of the current solution AND the ROADMAP.md update. I will respond with one of the following options:

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
```

</div>
