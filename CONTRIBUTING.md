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

1.  **Review the Roadmap & Specification:** Familiarize yourself with the [ROADMAP.json](ROADMAP.json) and [SPECIFICATION.md](SPECIFICATION.md) to understand the project's direction and goals. **Note that `ROADMAP.md` is automatically generated from `ROADMAP.json`. Do not edit `ROADMAP.md` directly! All roadmap contributions must be made by editing `ROADMAP.json`.**
2.  **Check for Existing Issues:** Before starting significant work, check the [issue tracker](link-to-github-issues) for existing issues related to your intended contribution. Comment on an existing issue or create a new one to discuss your plans and get feedback.
3.  **Fork the Repository:** Fork the `metamorphic-core` repository to your GitHub account.
4.  **Create a Branch:** Create a dedicated branch for your contribution (e.g., `feature/new-test-agent` or `fix/bug-in-llm-orch`).

5.  **Code Style & Quality:**

    *   Follow Python coding conventions (PEP 8).
    *   Write clear, well-commented code.
    *   Include unit and integration tests for new features and bug fixes.
    *   Ensure code is Flake8 compliant (run `flake8` locally).
    *   Use pre-commit hooks (recommended - see [README.md - Installation](#installation)).
    *   When working with the LLM code, adhere to the following structure guidelines:

        *   Ensure that code that exists remains. If code is no longer needed, there needs to be valid reasons, that should also not have security or ethical problems. Do not delete code just to save memory.
        *   Adhere to the file structure. Keep the tests in tests/ and make sure it can pass locally, before checking in.
        *   Use triple tabs, and give test commands in the description, for tests to be easily verifiable. Add logs to help verify, or show why the action might fail.

6.  **Submitting Code**

    *   Code is not directly written, but instead generated through the Driver and Coder models. For details, see `docs/workflows/markdown_automation.md`.

7.  **Toolchain Setup & Iterative Process**

    *   The Metamorphic Ecosystem development workflow is now largely automated via the Driver LLM. **With the completion of Phase 1.6, you initiate the process via the CLI (`python src/cli/main.py`), and the Driver autonomously selects tasks from `ROADMAP.json`, generates plans, invokes agents (including the Coder LLM for code generation), writes files, runs validation (tests, code review, security), generates a Grade Report, parses and evaluates it, and updates the roadmap status.**
    *   **With the completion of Phase 1.7, the Driver now attempts automated remediation for common validation failures (such as test failures, code style violations, and ethical transparency issues) based on the Grade Report feedback. You will need to manually address issues that automated remediation cannot fix, complex errors, design decisions, or tasks marked as "Blocked".**
    *   **With the completion of Phase 1.7 Task 1 (`task_1_7_1`), the recommended way to initiate this automated workflow is now using the `dev_run.py` script.** This script handles restarting the necessary Docker services and calling the main CLI.
    *   Your role involves:
        *   Ensuring Docker Desktop is running and the `metamorphic-core` service is available.
        *   **Initiating the workflow by running the `dev_run.py` script (`python dev_run.py`).**
        *   Monitoring the API server logs for progress, the full Grade Report, and the evaluation outcome (recommended action).
        *   Review the generated/modified code and the results of the automated validation steps as detailed in the logs/report.
        *   Check the updated `ROADMAP.json` status for the task.
        *   Manually addressing any issues that the Driver cannot resolve autonomously (e.g., complex errors, design decisions, tasks marked as "Blocked").
        *   Refining task descriptions in `ROADMAP.json` or providing manual fixes based on the Grade Report feedback before initiating the workflow again for the same task (if it wasn't marked "Completed").
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

*   **Multi-Dimensional Quality and Risk Assessment:** Your contribution will be rigorously assessed across multiple quality dimensions: Probability of Non-Regression, Probability of Test Success, Code Style Compliance Probability, Probability of Ethical Policy Compliance Probability, and Probability of Security Soundness.
*   **Probability Percentage Grades & Feedback:** For each dimension, a probability percentage grade will be assigned, reflecting the estimated confidence in that aspect of the contribution. You will receive an **Iterative Grading Report** with:

    *   **Overall Percentage Grade:** A combined grade reflecting overall quality and confidence. ***IMPORTANT:*** *Your goal is to achieve a 100% Overall Percentage Grade. Any grade below 100% indicates that further iteration and refinement are REQUIRED. You must use the dimension-specific feedback to improve your contribution and resubmit for review.*

        *   *The weights reflect the importance of each dimension. For example, Test Success receives the highest weighting, and code style gets the lowest weighting*
        *   *Therefore, if you are only able to achieve small gains in code style, but can achieve moderate gains in test success rate, you should focus on increasing the testing success rate.*
        *   Probability of Non-Regression: 20%
        *   Probability of Test Success: 30%
        *   Code Style Compliance Probability: 10%
        *   Probability of Ethical Policy Compliance Probability: 20%
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

### Contributing to the `ROADMAP.json` File <a name="contributing-to-roadmap-json"></a>

The `ROADMAP.json` file defines the project's development roadmap. It is *critical* that this file be well-formed and accurate. **The `ROADMAP.md` file is automatically generated from `ROADMAP.json`. DO NOT EDIT `ROADMAP.md` directly!** All roadmap contributions must be made by editing `ROADMAP.json`.

**`ROADMAP.json` Structure:**

The `ROADMAP.json` file must adhere to the following JSON structure. Any deviation from this structure will cause errors in the CI/CD pipeline or unexpected behavior.

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
            "status": "Not Started",
            "target_file": "optional/target/file.py",
            "depends_on": []
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
    *   `"target_file"`: **(Optional)** A string specifying the primary file path targeted by this task. This is used by the Driver for file operations. This *cannot* contain `/` or `..` sequences relative to the base path (to prevent path traversal vulnerabilities).
    *   `"depends_on"`: **(Optional)** A list of strings (task_ids) representing tasks that must be "Completed" before this task can be selected.
*   The `"phase"`, `"phase_goal"`, `"success_metrics"`, `"next_phase_actions"`, and `"current_focus"` fields are also required at the top level.

**Validation:**

*   Before submitting a pull request that modifies `ROADMAP.json`, please ensure that your changes are valid JSON and conform to the structure described above. You can use a JSON validator (many are available online) to check the syntax. The CI build includes similar validation, but it's always best to catch errors early.