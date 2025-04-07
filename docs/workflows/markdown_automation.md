# Markdown-Only Automation Workflow for Metamorphic Genesis Ecosystem

This document describes the "Markdown-Only Automation" workflow for developing the Metamorphic Software Genesis Ecosystem. This workflow leverages specially crafted prompts and augmented `.md` documentation files (ROADMAP.md, CONTRIBUTING.md) to guide an LLM to autonomously drive development tasks, with minimal direct prompting and strong emphasis on human oversight.

## Overview of the Workflow

The "Markdown-Only Automation" workflow aims to streamline development by enabling an LLM to:

1.  **Identify and select the next development task** from the project's [ROADMAP.md](ROADMAP.md) file.
2.  **Generate a complete proposed solution** for the selected task.
3.  **Perform a multi-dimensional self-assessment** of the proposed solution, using the "Iterative Grading Process" defined in [CONTRIBUTING.md](CONTRIBUTING.md).
4.  **Iteratively revise the solution** to achieve a "perfect grade" based on self-assessment feedback.
5.  **Generate clear "User Actionable Steps"** for implementing and verifying the solution.
6.  **Wait for user confirmation** before proceeding to the next task, ensuring human oversight at each step.

**Rationale for Prompt-Driven Workflow Change:**

To optimize the development process and leverage the unique strengths of different Large Language Models (LLMs), we have transitioned to a meta-planning and prompt generation approach. In this new workflow, I (the current LLM) will focus on project-level planning, task decomposition, and prompt generation. The actual code generation, testing, and execution will be handled by a more specialized LLM (e.g., Claude, GPT-4) that possesses superior coding capabilities. This change allows us to utilize my large context window for managing the overall project while delegating code-intensive tasks to an LLM that is better suited for those specific operations. This workflow will now require a 'Prompt Executor' to copy the prompt, and copy over the results after they are all said and done. This will provide for overall better, faster, and easier to obtain results.

This change does mean that you, as a developer, will need to manually run the generated prompts using a "Prompt Executor" function (described later) and then copy and paste the LLM's output back into the prompt for me to process. However, this extra step is expected to result in significantly improved code quality and faster development cycles.

This workflow is driven by a single, comprehensive prompt (detailed below) and relies heavily on **"LLM INSTRUCTION" blocks embedded within the `.md` documentation files** (ROADMAP.md and CONTRIBUTING.md).

## The "Ideal Self-Driving Prompt"

Here is the complete, ready-to-use "Ideal Self-Driving Prompt" for this workflow:

<div style="background-color:#e0f7fa; border: 2px solid #80deea; padding: 15px; margin-top: 10px; margin-bottom: 20px;">
<p style="font-family: monospace; font-size: 14px; line-height: 1.4;">

```
I have this codebase:
[INSERT YOUR CODEBASE HERE - PASTE THE ENTIRE CODEBASE AS TEXT]

I am providing these *.md files which drive the development process for this project:

[INSERT FULL CONTENT OF ROADMAP.MD FILE HERE]

[INSERT FULL CONTENT OF CONTRIBUTING.MD FILE HERE]

Please act as an autonomous development agent for this project.

Your task is to:

1. **Identify the next smallest, highest priority development task** from ROADMAP.md, following the "LLM INSTRUCTION: TASK SELECTION" block in that file.

2. **Generate a complete proposed solution** for this task, including code changes, documentation updates, etc., following the "LLM INSTRUCTION: SOLUTION GENERATION & SELF-ASSESSMENT" block in ROADMAP.md.

3. **Perform a self-assessment and grade your proposed solution** using the metrics and guidelines defined in the "Iterative Grading Process" section of CONTRIBUTING.md and the "LLM INSTRUCTION: CONTRIBUTION REVIEW GUIDANCE" block in CONTRIBUTING.md.  Generate a "Grade Report" in markdown format.

4. **If the self-assessment grade is not "perfect" (e.g., below 100% overall), revise your solution iteratively** based on the feedback generated during self-assessment until you achieve a "perfect" grade.  Re-grade after each revision and include the updated Grade Report.

5. **Once a "perfect grade" solution is achieved (or you have performed a reasonable number of revisions and reached a satisfactory grade if "perfect" is unattainable immediately), generate a complete set of "User Actionable Steps"** as a numbered list in markdown format, following the "LLM INSTRUCTION: USER ACTIONABLE STEPS" block in ROADMAP.md. Ensure these steps are safe and logically sound *before* implementing them. These steps should be clear and actionable for a developer to implement the proposed solution and verify its quality.

6. **After generating the "User Actionable Steps", also generate an "Updated ROADMAP.md Content" section containing the *entire content* of the ROADMAP.md file, but with the following updates:**
    *   **Mark the completed task as "✅ COMPLETE"** in the roadmap (e.g., append " - ✅ COMPLETE" to the task description in ROADMAP.md).
    *   **If all tasks within the *current phase* (e.g., "Phase 1.5 - Workflow Automation Side Project") are now marked "✅ COMPLETE", then:**
        *   **Generate a new, detailed breakdown of the *next* phase's (e.g., "Phase 2 - Iteration 1") tasks directly *below* the completed phase in the "Updated ROADMAP.md Content".**  Base this new breakdown on the high-level description of the next phase already present in ROADMAP.md (you may need to imagine or infer a logical task breakdown for the next phase).
        *   **"Archive" the completed phase's detailed task list:** Move the detailed task list of the *completed* phase to a new section at the end of the "Updated ROADMAP.md Content" called "**Archived Phase Roadmaps**" (create this section if it doesn't exist).  Clearly mark the archived section as "Archived: [Phase Name]" (e.g., "Archived: Phase 1.5 - Workflow Automation Side Project").
        *   **Update the "🎯 CURRENT FOCUS" section at the top of the "Updated ROADMAP.md Content"** to reflect the *next* active phase (e.g., "🎯 CURRENT FOCUS: PHASE 2 - Iteration 1 - Enhancements & Feature Expansion").

7. **Output the following in markdown format:**
    *   The selected task name and description.
    *   The complete "Grade Report" for your final (or best) solution.
    *   The complete, ready-to-implement "User Actionable Steps".
    * **The name and source of all files that will be generated.
    *   ** The llm code that will be used to create it should be something in the format of `A: execute_prompt(<YOUR CODE HERE>)`, all together in markdown code with the header.
    *   **"Updated ROADMAP.md Content"**:  Include the *full text content* of the updated `ROADMAP.md` file, incorporating the task completion marking and roadmap evolution as described in step 6.
    *   **Crucially:  End your response with the following choices:**

        *   **(A) Confirm:**  If the proposed changes are satisfactory and tests are passing (or there are no tests), implement the changes and proceed to the next task.  **Example:  `A: All tests passed. Implementing changes and moving on.`**
        *   **(B) Test(s) Not Passing:** If the proposed changes are implemented but tests are failing, provide detailed information about the failing tests. (Copy and paste the test output). **Example: `B: Test tests/test_api_mvp_endpoint.py::test_analyze_ethical_endpoint_no_code_integration failed with AssertionError: assert response.status_code == 200`**
        *   **(C) Missing File(s):** The proposed changes do not contain all files required, List the Missing Files and they will be added.. **Example: `C: Missing File(s): src/core/new_module.py, tests/test_new_module.py`**
        *   **(D) Ask Question:** If you want to ask the LLM a question about its approach or the proposed solution *before* implementing any changes. (State your question clearly). **Example: `D: Could you explain why you chose to use the 'dataclasses' module in this context?`**
        *   **(E) Code Issue:** If you have reviewed the code and see an error you want to point out. **Example: `E: It looks like the condition on Line 42 will always evaluate to false.`**
        *   **(F) Regenerate:** If you want the current task regenerated, include a very short prompt to explain why. **Example: `F: This code could be greatly simplified.`**

        **Important: Ensure all generated code adheres to the project's ethical policies and guidelines. For example, if the "BiasRisk" threshold is 0.1, make sure that no keyword identified in `policies/policy_bias_risk_strict.json` (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code.**

        **Your response MUST begin with one of the letters above (A, B, C, D, E or F) followed by a colon and a space, then your message.** For example: "B: Test test_my_function failed with assertion error..."

        **If your response DOES NOT begin with A, B, C, D, E, or F, or if you did not find a colon and space after the letter, the system will not know how to proceed. Please ensure your response follows the correct format. If I did not include all of the requested details, ask me to resend the full, un-truncated message.**

        (Waiting for user confirmation to implement changes and proceed to the next task)

8. **After providing the above output, WAIT for my confirmation before proceeding to any further tasks.** Do not automatically move to the next task until I explicitly confirm implementation of the current solution AND the ROADMAP.md update. **I will respond with one of the following options:**

    *   **"A: [Optional message if all tests passed, and implementing changes]"**
    *   **"B: [Detailed test output showing failing tests]"**
    *   **"C: [Missing File(s): list of missing files]"**
    *   **"D: [Your question to the LLM]"**
    *   **"E: [Describe a code issue you've found]"**
    *   **"F: [Reason for regenerating, e.g., 'Tests are too basic' or 'Code is inefficient']"**

   **Your response to my message should depend on the option I choose. Also, ensure all generated code adheres to ethical standards, guided by the `policies/policy_bias_risk_strict.json` example provided. If the "BiasRisk" threshold is 0.1, make sure that no keyword identified in that file's "keywords" list (["hate speech", "racist", "sexist", "offensive"]) is found in the generated code:**

    *   **If I respond with "A:", proceed to the next task as usual, after updating the ROADMAP.md.** If the response was unusually long or had issues with code, summarize the most important aspects. Also ask me to confirm the new files were added, if any.
    *   **If I respond with "B:", analyze the provided test output and revise the code to fix the failing tests. Re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".** Ensure all generated code adheres to project ethical standards.
    *   **If I respond with "C:", analyze the current code and create the missing files needed for the correct functioning of the changes. Then present the updated solution, including the list of files, re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".** Ensure all generated code adheres to project ethical standards.
    *   **If I respond with "D:", answer my question clearly and concisely. Do not proceed to the next task after answering. Simply wait for a new prompt from me.** If the response from me seems incomplete, ask me to provide the complete message again or re-send just the important data.
    *   **If I respond with "E:", analyze the code issue, revise the code to address the issue. Re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".** Ensure all generated code adheres to project ethical standards.
    *   **If I respond with "F:", regenerate the solution from scratch. Incorporate the reason for regeneration into your solution generation process. Re-run self-assessment and generate updated User Actionable Steps. Present the updated solution and "Grade Report".** Ensure all generated code adheres to project ethical standards.

    **If my response does NOT begin with A, B, C, D, E or F, output the following error message, then wait for further instructions: "ERROR: Invalid response format. Your response MUST begin with A, B, C, D, E, or F, followed by a colon and a space. If all of the relevant code or data is not provided, please include all of the content in the resent response or a truncated part."**
