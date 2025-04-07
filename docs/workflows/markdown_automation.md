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

6. **After generating the "User Actionable Steps", also generate an "Updated ROADMAP.md Content" section containing the *entire content* of the ROADMAP.md file, but with the following updates:**
    * **Mark the completed task as "✅ COMPLETE"** in the roadmap (e.g., append " - ✅ COMPLETE" to the task description in ROADMAP.md).
    * **If all tasks within the *current phase* (e.g., "Phase 1.5 - Workflow Automation Side Project") are now marked "✅ COMPLETE", then:**
        * **Generate a new, detailed breakdown of the *next* phase's (e.g., "Phase 2 - Iteration 1") tasks directly *below* the completed phase in the "Updated ROADMAP.md Content".**  Base this new breakdown on the high-level description of the next phase already present in ROADMAP.md (you may need to imagine or infer a logical task breakdown for the next phase).
        * **"Archive" the completed phase's detailed task list:** Move the detailed task list of the *completed* phase to a new section at the end of the "Updated ROADMAP.md Content" called "**Archived Phase Roadmaps**" (create this section if it doesn't exist).  Clearly mark the archived section as "Archived: [Phase Name]" (e.g., "Archived: Phase 1.5 - Workflow Automation Side Project").
        * **Update the "🎯 CURRENT FOCUS" section at the top of the "Updated ROADMAP.md Content"** to reflect the *next* active phase (e.g., "🎯 CURRENT FOCUS: PHASE 2 - Iteration 1 - Enhancements & Feature Expansion").

7. **Output the following in markdown format:**
    * The selected task name and description.
    * The complete "Grade Report" for your final (or best) solution.
    * The complete, ready-to-implement "User Actionable Steps".
    * **"Updated ROADMAP.md Content"**:  Include the *full text content* of the updated `ROADMAP.md` file, incorporating the task completion marking and roadmap evolution as described in step 6.
    * **Crucially:  End your response with the phrase:  "(Waiting for user confirmation to implement changes and proceed to the next task)"**

8. **After providing the above output, WAIT for my confirmation before proceeding to any further tasks.**  Do not automatically move to the next task until I explicitly confirm implementation of the current solution AND the ROADMAP.md update.

Begin now by identifying the next task from ROADMAP.md.
```
</p>
</div>
<p style="font-weight: bold; margin-top: -10px;">Important:</p><p style="font-family: monospace; font-size: 14px; line-height: 1.4; margin-top: -5px;">Remember to replace the bracketed placeholders with your actual codebase and `.md` file content.</p>

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

    Let's imagine we want to use the "Markdown-Only Automation Workflow" to initiate **Task 2.1: Implement `workflow_driver.py`** from our roadmap.

    1.  **Preparation:** We have our codebase, `ROADMAP.md`, and `CONTRIBUTING.md` files ready in our project directory.
    2.  **Copy "Ideal Self-Driving Prompt":** We copy the "Ready-to-Use "Ideal" Self-Driving Prompt" from this document.
    3.  **Paste into LLM Interface:** We paste the prompt into our chosen LLM interface (e.g., the Gemini Pro web UI).
    4.  **Replace Placeholders:** **Crucially, we replace the placeholders** in the prompt with the *actual text content* of our project files:
        *   `[INSERT YOUR CODEBASE HERE...]` is replaced with the *entire text content* of all files in our codebase (e.g., copy-paste the text of `.env.example`, `.github/workflows/ci.yml`, etc. all the way to `tests/test_unit_components.py`).
        *   `[INSERT FULL CONTENT OF ROADMAP.MD FILE HERE]` is replaced with the *full text content* of our `ROADMAP.md` file.
        *   `[INSERT FULL CONTENT OF CONTRIBUTING.MD FILE HERE]` is replaced with the *full text content* of our `CONTRIBUTING.md` file.
    5.  **Send the Prompt:** We send the filled-in prompt to the LLM.
    6.  **Review LLM Output:** The LLM generates a response.  A snippet of the *expected output* for this specific task might look like this (the actual output may vary slightly):

```markdown
```markdown
**Selected Task:** Task 2.1 (Week 7 - 2 days): Implement `workflow_driver.py` with prompt generation, LLM interaction, and basic output parsing.

**Grade Report:**

```markdown
### Grade Report: Initial Solution for Task 2.1 - Implement `workflow_driver.py`

**Overall Percentage Grade:** 80%

**Dimension-Specific Probability Percentages:**

*   Probability of Non-Regression: 85%
*   Probability of Test Success: 70%
*   Code Style Compliance Probability: 95%
*   Ethical Policy Compliance Probability: 90%
*   Probability of Task Completion: 90%

**Actionable Feedback for Improvement:**

*   ... (Feedback details as in the previous Grade Report example) ...
```

**User Actionable Steps:**

```markdown
### User Actionable Steps for Task 2.1 - Implement `workflow_driver.py`

1.  **Create `workflow_driver.py` file:**
    *   ... (Code snippet for `workflow_driver.py` as in previous example) ...

2.  **Modify `run_genesis.py`:**
    *   ... (Code snippet for `run_genesis.py` as in previous example) ...

3.  ... (Rest of the User Actionable Steps as in previous example) ...
```

(Waiting for user confirmation to implement changes and proceed to the next task)
```

    7.  **Implement User Actionable Steps:** We review the "User Actionable Steps" provided by the LLM. If they seem reasonable and safe, we implement them in our codebase. In this example, we would create `workflow_driver.py` and modify `run_genesis.py`.
    8.  **Provide Confirmation:**  After implementing the steps and (ideally) running the suggested unit tests (if any are generated or if we create them ourselves), we provide confirmation to the LLM, such as: "Confirmed - implemented changes for Task 2.1 and run unit tests."
    9.  **Repeat for Next Task:** To move to the next task, we simply re-submit the *same* "Ideal Self-Driving Prompt" to the LLM, potentially with a minimal prompt like: "OK, proceed to the next task."

    **Customization and Refinement:**

    *   **Experiment with Different LLMs:** While the "Ideal Self-Driving Prompt" is designed to be general-purpose, you may find that different LLMs (e.g., Gemini Pro, GPT-4, Claude, or open-source models) respond differently to the prompt and the "LLM INSTRUCTION" blocks.  Experiment with different models to see which provides the best results for your specific development tasks and coding style. Some models are known to be particularly good at following complex instructions.
    *   **Tailor Prompts for Task Types:** For very specific or complex tasks, you might consider slightly adjusting the "Ideal Self-Driving Prompt." For example, if you are focusing on documentation tasks, you could add specific instructions related to documentation quality or format.  If you are working on a particularly security-sensitive area, you might emphasize security considerations in the prompt.
    *   **Iteratively Refine "LLM INSTRUCTION" Blocks:** The "LLM INSTRUCTION" blocks within `ROADMAP.md` and `CONTRIBUTING.md` are designed to be flexible and adaptable. As you use the workflow and observe the LLM's behavior, you may identify areas where the instructions could be clearer, more specific, or better aligned with your project's needs.  Don't hesitate to iteratively refine these instruction blocks to improve the workflow's effectiveness over time.
    *   **Experiment with LLM Parameters (Advanced):** For more advanced customization, you can experiment with LLM parameters within the "Ideal Self-Driving Prompt" itself (if your LLM interface allows it).  Parameters like `temperature` and `top_p` can influence the creativity and determinism of the LLM's responses.  Lower temperatures generally lead to more deterministic and focused responses, while higher temperatures can introduce more creativity and exploration.  However, for this workflow, a moderate temperature (around 0.6-0.8) is generally recommended to balance instruction following and solution generation.

    **Limitations:**

    [Clearly state the limitations of the "Markdown-Only Automation" workflow, such as context window limits, reliance on LLM instruction following, and the need for human oversight. *(You can add this section later - for now, focus on getting the basic documentation in place)*]

    **Conclusion:**

    The "Markdown-Only Automation" workflow offers a streamlined and accessible approach to AI-assisted development for the Metamorphic Software Genesis Ecosystem. By leveraging the power of LLMs and carefully designed documentation, it aims to accelerate development while maintaining quality, transparency, and human control.

---