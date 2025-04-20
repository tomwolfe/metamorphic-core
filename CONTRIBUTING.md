# Contributing to the Metamorphic Software Genesis Ecosystem <a name="contributing"></a>

We enthusiastically welcome contributions to the Metamorphic Software Genesis Ecosystem! Whether you are interested in core development, ethical policy design, security enhancements, documentation, or community engagement, your contributions are valuable.

**Contribution Areas:**

1.  **Core Code Development:**
    *   Enhance existing AI agents (e.g., `CodeGenerationAgent`, `TestGenerationAgent`, `SecurityAgent`).
    *   Implement new agents or sub-modules (e.g., for formal verification, quantum computing integration, UI/UX).
    *   Improve core framework components (e.g., Knowledge Graph, LLM Orchestration, Ethical Governance Engine).
    *   Optimize performance, security, and resource efficiency.

2.  **Ethical Governance & Policy:**
    *   Design and propose new ethical policies (JSON format) for various domains and risk levels.
    *   Contribute to the Ethical Policy Schema (`ethical_policy_schema.json`).
    *   Develop bias detection and mitigation strategies.
    *   Enhance transparency and explainability features.

3.  **Security Enhancements:**
    *   Develop new security agents or security checks (SAST, DAST, etc.).
    *   Contribute to security best practices and guidelines.
    *   Help identify and remediate potential vulnerabilities.

4.  **Documentation:**
    *   Improve and expand existing documentation (API docs, specifications, roadmaps, tutorials).
    *   Create new documentation (e.g., examples, use cases, architectural diagrams).
    *   Translate documentation into other languages (localization).

5.  **Community Engagement & Support:**
    *   Help answer questions and provide support to other community members.
    *   Share your use cases and experiences with the Metamorphic Ecosystem.
    *   Contribute to community forums, discussions, and events (planned).
    *   Help with community building and outreach.

**Contribution Guidelines:**

1.  **Review the Roadmap & Specification:** Familiarize yourself with the [ROADMAP.json](ROADMAP.json) and [SPECIFICATION.md](SPECIFICATION.md) to understand the project's direction and goals. **Note that `ROADMAP.md` is automatically generated from `ROADMAP.json`.  Do not edit `ROADMAP.md` directly! All roadmap contributions must be made by editing `ROADMAP.json`.**
2.  **Check for Existing Issues:** Before starting significant work, check the [issue tracker](link-to-github-issues) for existing issues related to your intended contribution. Comment on an existing issue or create a new one to discuss your plans and get feedback.
3.  **Fork the Repository:** Fork the `metamorphic-core` repository to your GitHub account.
4.  **Create a Branch:** Create a dedicated branch for your contribution (e.g., `feature/new-test-agent` or `fix/bug-in-llm-orch`).

5.  **Code Style & Quality:**

    *   Follow Python coding conventions (PEP 8).
    *   Write clear, well-commented code.
    *   Include unit and integration tests for new features and bug fixes.
    *   Ensure code is Flake8 compliant (run `flake8` locally.
    *   Use pre-commit hooks (recommended - see [INSTALL.md](INSTALL.md)).
    *   When working with the LLM code, adhere to the following structure guidelines:

        *   Ensure that code that exists remains. If code is no longer needed, there needs to be valid reasons, that should also not have security or ethical problems. Do not delete code just to save memory.
        *   Adhere to the file structure. Keep the tests in tests/ and make sure it can pass locally, before checking in.
        *   Use triple tabs, and give test commands in the description, for tests to be easily verifiable. Add logs to help verify, or show why the action might fail.

6.  **Submitting Code**

    *   Code is not directly written, but instead generated through the Driver and Coder models. For details, see `docs/workflows/markdown_automation.md`.

7.  **Toolchain Setup & Iterative Process**

    *   The Metamorphic Ecosystem development workflow is now largely automated via the Driver LLM. You initiate the process via the CLI (`python src/cli/main.py`), and the Driver autonomously selects tasks, generates plans, invokes agents (including the Coder LLM for code generation), writes files, runs validation (tests, code review, security), generates a Grade Report, and updates the roadmap status.
    *   Your role involves:
        *   Ensuring the API server is running.
        *   Initiating the workflow via the CLI.
        *   Monitoring the logs for progress, Grade Reports, and User Actionable Steps (if any).
        *   Reviewing the generated/modified code and the results of the automated validation steps.
        *   Providing feedback to the Driver LLM via the specified response codes if manual intervention or clarification is needed.
        *   Manually addressing any issues that the Driver cannot resolve autonomously (e.g., complex errors, design decisions).
    *   You no longer need to manually copy and paste code blocks between the Driver and Coder LLMs or manually run tests/linters for every iteration – these steps are automated.

8.  **Submit a Pull Request (PR):**

    *   Once your contribution (which may consist of code generated by the Driver, manual fixes, or updates to documentation/policies) is ready, submit a pull request to the `main` branch of the `metamorphic-core` repository.
    *   Clearly describe the purpose and scope of your contribution in the PR description.
    *   Reference any related issues in the PR description (e.g., "Fixes #123", "Implements feature requested in #456").

9.  **Code Review & Iteration:**

    *   Your pull request will be reviewed by project maintainers using an **Iterative Grading Process** (see [CONTRIBUTING.md - Contribution Review Process: Iterative Probability-Based Grading](CONTRIBUTING.md#contribution-review-process-iterative-probability-based-grading)).
    *   Be responsive to feedback and be prepared to iterate on your contribution to address review comments and improve code quality.
    *   Code review is focused on code quality, correctness, security, ethical considerations, and alignment with project goals, as evaluated through the **Iterative Grading Process**.

### Contribution Review Process: Iterative Probability-Based Grading

To maintain the high quality standards of the Metamorphic Software Genesis Ecosystem, we use an iterative review process for all contributions, based on **Multi-Dimensional Grading**. When you submit a contribution, it will be evaluated using this process, which involves:

*   **Multi-Dimensional Quality and Risk Assessment:** Your contribution will be rigorously assessed across multiple quality dimensions: Probability of Non-Regression, Probability of Test Success, Code Style Compliance Probability, Ethical Policy Compliance Probability, and Probability of Security Soundness.
*   **Probability Percentage Grades & Feedback:** For each dimension, a probability percentage grade will be assigned, reflecting the estimated confidence in that aspect of the contribution. You will receive an **Iterative Grading Report** with:

    *   **Overall Percentage Grade:** A combined grade reflecting overall quality and confidence. ***IMPORTANT:*** *Your goal is to achieve a 100% Overall Percentage Grade. Any grade below 100% indicates that further iteration and refinement are REQUIRED.  You must use the dimension-specific feedback to improve your contribution and resubmit for review.*

        *   *The weights reflect the importance of each dimension. For example, Test Success receives the highest weighting, and code style gets the lowest weighting*
        *   *Therefore, if you are only able to achieve small gains in code style, but can achieve moderate gains in test success rate, you should focus on increasing the testing success rate.*
        *   Probability of Non-Regression: 20%
        *   Probability of Test Success: 30%
        *   Code Style Compliance Probability: 10%
        *   Ethical Policy Compliance Probability: 20%
        *   Probability of Security Soundness: 20%
    *   **Dimension-Specific Probability Percentages:** Individual percentage grades for each quality dimension (Non-Regression, Test Success, Code Style, Ethics, Security).
    *   **Actionable Feedback:** Detailed feedback for each dimension, explaining the rationale behind the grades and providing concrete steps for improvement.
    *   **Guidance for Code Style Compliance Probability**:
        *   Aim to resolve all issues to have 100% score
        *   Each warning will detract from quality, even if low risk.
        *   Do not ignore any code issues, fix the problems and resolve all complaints.
    *   **Guidance for Ethical Policy Compliance Probability**:
        *   Aim for 100% compliance
        *   Apply an ethical framework to ensure that the generated code respects human values and rights.
        *   Any code generated that has a violation must be seen as a severe issue, as the AI is responsible for following this component.
        *   Take feedback and use the appropriate policy to verify compliance.
        *   Review code and ensure it adheres to high transparency.
    *   **Guidance for Non-Regression and Test Success**
        *   Provide accurate reports and testing results for each file you write.
        *   This is what the driver will use to determine if the outcome was successful.

*   **Iterative Improvement:** We encourage you to use this feedback to refine your contribution and resubmit for review. The goal is to work iteratively, using the feedback to increase the probability percentages across all dimensions and achieve a 100% overall grade. This collaborative process ensures that all contributions meet our rigorous quality benchmarks and contribute to a robust and reliable system.

<div style="background-color:#f0f0f0; border: 1px solid #ccc; padding: 10px;">
**--- LLM INSTRUCTION: CONTRIBUTION REVIEW GUIDANCE ---**

**LLM INSTRUCTION: When acting as a "reviewer" for a hypothetical code contribution (based on a task from ROADMAP.json),  use the "Iterative Grading Process" described above, paying particular attention to the "Multi-Dimensional Quality and Risk Assessment". Specifically:**

1.  **Assume you have received a code contribution (imagine it's for the task you selected from ROADMAP.json).**
2.  **Perform a "Multi-Dimensional Grading" of this hypothetical contribution, rigorously assessing it across the following quality dimensions (as defined in detail in the "Iterative Grading Process" section):**

    *   Probability of Non-Regression
    *   Probability of Test Success
    *   Code Style Compliance Probability
    *   Ethical Policy Compliance Probability
    *   Probability of Security Soundness

3.  **For each dimension, assign a probability percentage grade (0-100%) and provide actionable feedback (as if you were giving feedback to a developer, focusing on concrete steps to improve the grade).**

    *   **Actionable feedback Examples: Probability of Non-Regression:**

        *   Add unit tests that have over 95% branch test coverage.
        *   Analyze the output and see what code blocks are potentially failing.
        *   Check which code blocks change most of the high order functions, and see how that could affect the output.

    *   **Actionable feedback Examples: Probability of Test Success:**

        *   Address testing frameworks that may not work, and verify test pass with a secondary review.
        *   When creating tests, the tests should be accurate and account for any edge cases that are missed.
        *   The tests need to have minimal mocking code, and directly test functionality rather than mocking functionality.

    *   **Actionable feedback Examples: Code Style Compliance Probability:**

        *   Lint code, and follow established linting standards.
        *   Ensure that all code follows python guidelines.
        *   For any code that deviates from python guidelines, resolve this prior to finishing the code.

    *   **Actionable feedback Examples: Ethical Policy Compliance Probability:**

        *   Address the code and ensure it doesn't have problems, or the LLM cannot be allowed to generate code as it could lead to more problems.
        *   All code needs to be within guidelines
        *   There is no reason for code to violate these requirements, and this must always be addressed.
        *   Take feedback and use the appropriate policy to verify compliance.
        *   Review code and ensure it adheres to high transparency.

    *   **Actionable feedback Examples: Probability of Security Soundness:**

        *   Security is of the highest importance
        *   No code is too inefficient to be secure, all code must pass security review.
        *   Implement industry standard methods to verify security.

4.  **Calculate an "Overall Percentage Grade" based on the dimension-specific grades (consider using a weighted average if certain dimensions are more critical for this specific task). Weights are defined in the "Probability Percentage Grades & Feedback" section.**

5.  **Generate a structured "Grade Report" in markdown format, designed for developer actionability. The report should include:**

    *   ***IMPORTANT:*** *Any Grade Report that is not 100% requires that you use these findings to generate updated code. Ensure that your next call to write_file contains the code with these revisions. You must also include the Grade Report in the generated output as a JSON object.*
    *   Overall Percentage Grade
    *   Dimension-Specific Probability Percentages: For each dimension, state the percentage grade and provide a clear justification for this grade, referencing specific aspects of the hypothetical contribution.
    *   Actionable Feedback for each dimension: Provide concrete, step-by-step feedback for each dimension, explaining *how* the developer can improve their contribution to increase the probability percentage and reach a 100% overall grade. This feedback should be directly linked to the quality dimensions and the "Iterative Grading Process". *Be sure to reference the "Actionable Insights for Phase 1.6" from the [Competitive Landscape Analysis](COMPETITIVE_LANDSCAPE.md#actionable-insights-for-phase-1-6) when providing feedback related to project goals and priorities.*

**Example Grade Report:**
+***IMPORTANT:*** *Any Grade Report that is not 100% requires that you use these findings to generate updated code. Ensure that your next call to write_file contains the code with these revisions.*
*   Overall Percentage Grade: 92%

    *   Probability of Non-Regression: 90% - Excellent test coverage for core logic. Potential impact on module X needs further review.

        *   *Actionable Feedback: Review module X to verify test validity.*

### Contributing to the `ROADMAP.json` File <a name="contributing-to-roadmap-json"></a>

The `ROADMAP.json` file defines the project's development roadmap.  It is *critical* that this file be well-formed and accurate. **The `ROADMAP.md` file is automatically generated from `ROADMAP.json`. DO NOT EDIT `ROADMAP.md` directly!** All roadmap contributions must be made by editing `ROADMAP.json`.

**`ROADMAP.json` Structure:**

The `ROADMAP.json` file must adhere to the following JSON structure.  Any deviation from this structure will cause errors in the CI/CD pipeline or unexpected behavior.

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

### File Format Considerations
*   `ROADMAP.md` - see `docs/workflows/markdown_automation.md` for file format and formatting requirements. **The `ROADMAP.md` file is now automatically generated from `ROADMAP.json`.  DO NOT EDIT THIS FILE DIRECTLY!** All roadmap contributions must be made by editing `ROADMAP.json`. See `docs/workflows/markdown_automation.md` for details on the `ROADMAP.json` format and how to contribute to the roadmap.
