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

6. **Output the following in markdown format:**
    * The selected task name and description.
    * The complete "Grade Report" for your final (or best) solution.
    * The complete, ready-to-implement "User Actionable Steps".
    * **Crucially:  End your response with the phrase: "(Waiting for user confirmation to implement and proceed to the next task)"**

7. **After providing the above output, WAIT for my confirmation before proceeding to any further tasks.**  Do not automatically move to the next task until I explicitly confirm implementation of the current solution.

Begin now by identifying the next task from ROADMAP.md.
```
</p>
</div>

    **Understanding "LLM INSTRUCTION" Blocks:**

    A key aspect of this workflow is the use of specially formatted **"LLM INSTRUCTION" blocks** within the [ROADMAP.md](ROADMAP.md) and [CONTRIBUTING.md](CONTRIBUTING.md) files. These blocks (demarcated by `--- LLM INSTRUCTION ---` and `--- END LLM INSTRUCTION ---` within `<div>` tags for visual emphasis) serve as **explicit directives for the LLM**.

    The "Ideal Self-Driving Prompt" is designed to instruct the LLM to **specifically read and follow the instructions contained within these "LLM INSTRUCTION" blocks**.  This allows us to embed detailed workflow logic and guidance directly within the project's documentation, making the documentation itself "executable" by the LLM.

    **Key "LLM INSTRUCTION" Blocks and Their Roles:**

    *   **`ROADMAP.md` - "LLM INSTRUCTION: TASK SELECTION":**  Instructs the LLM on how to identify and prioritize the next development task from the roadmap.
    *   **`ROADMAP.md` - "LLM INSTRUCTION: SOLUTION GENERATION & SELF-ASSESSMENT":**  Guides the LLM on how to generate a solution for the selected task and perform a multi-dimensional self-assessment, using the metrics defined in the Iterative Grading Process.
    *   **`ROADMAP.md` - "LLM INSTRUCTION: USER ACTIONABLE STEPS":**  Directs the LLM to generate clear, actionable steps for a human developer to implement and verify the proposed solution.
    *   **`CONTRIBUTING.md` - "LLM INSTRUCTION: CONTRIBUTION REVIEW GUIDANCE":**  Provides instructions for the LLM when it is acting as a "reviewer," guiding it to use the "Iterative Grading Process" and the multi-dimensional grading metrics for evaluating hypothetical code contributions.

    **Workflow - Step-by-Step Guide:**

    1.  **Prepare your Environment:** Ensure you have your codebase, `ROADMAP.md`, and `CONTRIBUTING.md` files ready.
    2.  **Copy the "Ideal Self-Driving Prompt":** Copy the "Ready-to-Use "Ideal" Self-Driving Prompt" from this document.
    3.  **Paste into LLM Interface:** Paste the prompt into your chosen LLM interface (e.g., web UI, API client).
    4.  **Replace Placeholders:** **Crucially, replace the placeholder sections** `[INSERT YOUR CODEBASE HERE...]`, `[INSERT FULL CONTENT OF ROADMAP.MD FILE HERE]`, and `[INSERT FULL CONTENT OF CONTRIBUTING.MD FILE HERE]` in the prompt with the *actual text content* of your project.
    5.  **Send the Prompt:** Submit the filled-in prompt to the LLM.
    6.  **Review LLM Output:** Carefully examine the LLM's response. It should include:
        *   The selected task name and description.
        *   A detailed "Grade Report" with self-assessment.
        *   A numbered list of "User Actionable Steps."
        *   The "(Waiting for user confirmation...)" message.
    7.  **Implement User Actionable Steps:** If you are satisfied with the LLM's proposed solution, implement the "User Actionable Steps" in your codebase.
    8.  **Provide Confirmation:**  Once implemented, provide confirmation to the LLM (e.g., "Confirmed - implemented changes").
    9.  **Repeat for Next Task:** To move to the next task, simply re-submit the *same* "Ideal Self-Driving Prompt" to the LLM, potentially with a minimal prompt like: "OK, proceed to the next task."

    **Example Usage Scenario:**

    [Include a brief example of how to use the prompt, showing a hypothetical interaction and the expected output from the LLM.  *(You can add this section later - for now, focus on getting the basic documentation in place)*]

    **Customization and Refinement:**

    [Provide tips on how users can customize the prompt, experiment with different LLMs, and refine the workflow over time. *(You can add this section later - for now, focus on getting the basic documentation in place)*]

    **Limitations:**

    [Clearly state the limitations of the "Markdown-Only Automation" workflow, such as context window limits, reliance on LLM instruction following, and the need for human oversight. *(You can add this section later - for now, focus on getting the basic documentation in place)*]

    **Conclusion:**

    The "Markdown-Only Automation" workflow offers a streamlined and accessible approach to AI-assisted development for the Metamorphic Software Genesis Ecosystem. By leveraging the power of LLMs and carefully designed documentation, it aims to accelerate development while maintaining quality, transparency, and human control.

---

