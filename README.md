# Metamorphic Software Genesis Ecosystem

[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-AGPLv3-blue.svg)](LICENSE)
[![Roadmap Status](https://img.shields.io/badge/Roadmap-Phase_1.6_COMPLETED-green)](ROADMAP.md)

**🎯 CURRENT FOCUS: PHASE 2 Iteration 2 - Enhanced Agents & Knowledge Graph 🧠**

The Metamorphic Software Genesis Ecosystem is an AI-driven framework designed to autonomously generate, maintain, and evolve secure, ethical, and high-performance software solutions from high-level specifications. It continuously refines its capabilities through feedback and self-improvement.

We are excited to announce the successful completion of **Phase 1.6: Enhanced Workflow Automation!** Building upon the core autonomous Driver loop established in Phase 1.5, Phase 1.6 implemented the crucial end-to-end automation layer. This includes automating workflow initiation via CLI/API, executing validation steps (tests, code review, security) directly within the Driver loop, processing the Grade Report, and automatically updating the roadmap status.

**With Phase 1.6 complete, Metamorphic Core now features a robust, self-driving development loop.** This significantly accelerates iteration cycles, improves consistency, and provides a solid foundation for integrating more advanced AI capabilities. We are now transitioning into **Phase 2 Iteration 2**, focusing on significantly enhancing core AI agents (Test Generation, Code Review) and integrating them with an expanded Knowledge Graph for improved context management and generation quality. See the [Roadmap](#further-documentation) for details.

---

**Strategic Impact of Phase 1.6:**

Phase 1.6 focused on completing the end-to-end automation layer by automating workflow initiation, validation execution, feedback processing, and roadmap status updates. **With the successful completion of Phase 1.6, we have established a robust, self-driving development loop that significantly accelerates iteration cycles and improves the consistency and reliability of the development process.** This strategic investment in our own development process is crucial before proceeding to Phase 2's focus on enhancing agent intelligence and Knowledge Graph integration. This also supports more robust and reliable AI-driven code generation and validation by ensuring automated feedback loops are closed.

**Three-Stage Approach to Markdown-Only Automation (Completed in Phase 1.5 & 1.6):**

Phase 1.5 established the fundamental markdown automation workflow and CLI driver, achieving autonomous execution of development tasks (task selection, planning, agent invocation, file writing) once initiated. **Phase 1.6 built upon this by automating the initiation via CLI/API, integrating automated execution of validation steps (tests, code review, security), parsing the Grade Report, and automatically updating the roadmap status.** The workflow is now fully automated from initial CLI command through validation and roadmap update.

**Estimated Potential Benefits (Long-Term, Full Integration):**

*   **MSGE (Without Phase 1.5/1.6):** Represents a baseline system with manual operations and loosely coupled components, delivering a starting-point project success likelihood of 65%.
*   **Phase 1.5 (Completed):** Successfully automated key routine workflow operations (task processing, agent invocation, file writing), improving developer experience by an estimated 85% in those specific tasks once fully integrated.
*   **Phase 1.6 (Completed):** Completed the end-to-end automation loop (initiation, validation execution, reporting, status update), significantly enhancing the overall efficiency, consistency, and reliability of the autonomous development process. This is estimated to contribute a further 10-15% improvement in overall developer efficiency and project success likelihood compared to Phase 1.5 alone.
*   **MSGE (With Phase 1.6):** The long-term objective is a fully integrated system achieving up to a 95% grade in overall developer efficiency. Faster iteration cycles and more consistent code quality are expected. Successful execution of the Markdown-Only Automation Workflow is intended to enhance adherence to evolving ethical standards.

---

**Table of Contents**

*   [About the Metamorphic Software Genesis Ecosystem](#about)
*   [Getting Started](#getting-started)
    *   [Prerequisites](#prerequisites)
    *   [Installation](#installation)
        *   [.env Configuration & API Keys](#env-configuration-api-keys)
    *   [Running the API Server](#running_the_api_server)
    *   [Quickstart Guide](#quickstart_guide)
    *   [System Requirements](#system-requirements)
    *   [Quickstart Guide to Automated Workflow](#quickstart-guide-to-automated-workflow)
*   [Workflow and Use Case Example](#workflow-use-case-example)
*   [Core API Endpoints](#core-api-endpoints)
*   [Contributing](#contributing)
*   [Further Documentation](#further-documentation)
*   [Troubleshooting](#troubleshooting)
*   [License](#license)
*   [Contact](#contact)
*   [Disclaimer](#disclaimer)

---

## <a name="about"></a>About the Metamorphic Software Genesis Ecosystem

The Metamorphic Software Genesis Ecosystem is an AI-driven framework designed to autonomously generate, maintain, and evolve secure, ethical, and high-performance software solutions from high-level specifications. It continuously refines its capabilities through feedback and self-improvement. **A key strategic decision was the implementation of Phase 1.5 and Phase 1.6, which are now complete.** Phase 1.5 focused on improving the *development process itself* by implementing a Markdown-Only Automation Workflow. **With the successful completion of Phase 1.5 Stage 3, the core Driver LLM loop is now automated, enabling autonomous task selection, planning, agent invocation, and file writing.** **Phase 1.6 completed the end-to-end automation layer by automating workflow initiation, validation execution, feedback processing, and roadmap status updates.** This is aimed at faster testing, rapid prototyping and easier iterative grading, and will amplify the value and efficiency of the overall system. We are now focused on **Phase 2 Iteration 2: Enhanced Agents & Knowledge Graph**, focusing on significantly enhancing core AI agents (Test Generation, Code Review) with deeper code understanding and integrating them with an expanded Knowledge Graph for improved context management and generation quality.

**Key Objectives:**

*   **Autonomous Generation:** Create functional applications from natural language or structured specifications.
*   **Ethical Governance:** Enforce configurable ethical policies throughout development.
*   **Automated Quality & Security:** Integrate continuous testing, code review, and formal verification.
*   **Self-Improving Development Process:** Optimize its own development using AI-driven planning.
*   **Self-Improvement:** Learn from analysis, feedback, and metrics to enhance its core capabilities.

*(For the full detailed vision and architecture, see [**SPECIFICATION.md**](SPECIFICATION.md))*

## <a name="getting-started"></a>Getting Started

### <a name="prerequisites"></a>Prerequisites

*   **Python Version:** Python 3.11+. Verify with `python --version`.
*   **Docker:** Docker Desktop (optional, but highly recommended for Redis/ZAP services). See [Troubleshooting](#troubleshooting) for Docker issues.
*   **API Keys:** Required API keys (see [.env Configuration & API Keys](#env-configuration-api-keys)).
*   **Git:** Git installed on your system.

### <a name="installation"></a>Installation

1.  **Verify Python Version:** Run `python --version` to ensure it's 3.11+.
2.  **Clone Repository:**
    ```bash
    git clone https://github.com/tomwolfe/metamorphic-core.git && cd metamorphic-core
    ```
3.  **Configure Environment Variables:**
    ```bash
    cp .env.example .env
    # Edit .env with your API keys (see .env Configuration & API Keys below)
    ```
4.  **Start Optional Services (Redis & ZAP with Docker Compose):**
    ```bash
    docker-compose up -d redis zap  # Ensure Docker Desktop is running
    ```
5.  **Create and Activate Virtual Environment:**
    ```bash
    python -m venv venv
    source venv/bin/activate  # Linux/macOS
    # venv\Scripts\activate  # Windows
    ```
6.  **Install Python Dependencies:**
    ```bash
    pip install --upgrade pip
    pip install -r requirements/base.txt
    pip install -r requirements/dev.txt # For development tools like Flake8 and pre-commit
    ```
7.  **Install and Set up Pre-commit Hooks (Optional, Recommended):**
    ```bash
    pip install pre-commit
    pre-commit install
    ```

#### <a name="env-configuration-api-keys"></a>.env Configuration & API Keys

1.  **Create `.env` File:** Copy `.env.example` to `.env`: `cp .env.example .env`
2.  **Set Required Gemini API Key:**

    *   Edit `.env` and set `GEMINI_API_KEY=your_gemini_api_key` with your Gemini API key from [Google AI Studio](https://ai.google.dev/). **This is required for the core functionality.**
3.  **Configure Optional API Keys (in `.env`):**

    *   `HUGGING_FACE_API_KEY`: For Hugging Face models (from [Hugging Face](https://huggingface.co/settings/tokens)).
    *   `YOUR_GITHUB_API_KEY`: For future GitHub integrations (from [GitHub](https://github.com/settings/tokens)).
    *   `ZAP_API_KEY`: For local ZAP security scans (advanced, optional) - default is `changeme`.
4.  **Optional Settings (in `.env`):**

    *   `LLM_PROVIDER`, `LLM_MAX_RETRIES`, `LLM_TIMEOUT`, `HUGGING_FACE_MODEL`, `DOCKERHUB_USERNAME` (see `.env.example` for details).
5.  **Security Note:** **Never commit your `.env` file** to version control. Ensure `.env` is in `.gitignore`.

### <a name="running_the_api_server"></a>Running the API Server

```bash
# Ensure .env is configured and venv is active
python src/api/server.py
```
Keep this terminal window open. The API server must be running for the CLI workflow to function.

The server will run at `http://127.0.0.1:5000/`. Check its health at `http://127.0.0.1:5000/genesis/health`.

### <a name="quickstart_guide"></a>Quickstart Guide

Test the core API endpoint after installation and server startup:

```bash
curl -X POST \
  http://127.0.0.1:5000/genesis/analyze-ethical \
  -H "Content-Type": "application/json" \
  -d '{"code": "def calculate_area(radius):\n    \"\"\"Calculates the area of a circle.\"\"\"\n    if radius < 0:\n        raise ValueError(\"Radius cannot be negative\")\n    return 3.14159 * radius * radius"}'
```

Examine the JSON response for `code_quality` and `ethical_analysis` sections.

### <a name="system-requirements"></a>System Requirements

*   **Operating System:** Linux (Ubuntu recommended), macOS, Windows (Windows 10/11 tested).
*   **Python Version:** Python 3.11+ (required).
*   **Docker:** Optional (recommended for services). See [Troubleshooting](#troubleshooting) for Docker issues.
*   **RAM:** 8GB RAM minimum, 16GB+ recommended for LLM features.
*   **Disk Space:** 2GB free disk space or more.

### <a name="quickstart-guide-to-automated-workflow"></a>Quickstart Guide to Automated Workflow

With Phase 1.6 complete, the Metamorphic Core offers a streamlined, AI-driven development experience via its **Automated Workflow**. This workflow leverages the Driver LLM to autonomously manage tasks from your `ROADMAP.json`, including code generation, validation, and status updates.

**Quickstart Steps (Post-Phase 1.6):**

1.  **Ensure the API server is running** (`python src/api/server.py`). Keep this terminal window open.
2.  **Prepare `ROADMAP.json`:** Ensure your `ROADMAP.json` file is correctly formatted and contains at least one task with the status `"Not Started"`. The Driver will automatically select the first such task it finds.
3.  **Initiate the Automated Workflow via CLI:** Open a *new* terminal in the project root and run the CLI command:
    ```bash
    python src/cli/main.py
    ```
    *   *(Optional)* Specify a different roadmap file: `python src/cli/main.py --roadmap path/to/your/roadmap.json`
    *   *(Optional)* Specify an output directory (where files like the Grade Report might be written, though code files are typically written to their source paths): `python src/cli/main.py --output-dir ./my_output`
4.  **Monitor the API Server Logs:** Switch back to the terminal running the API server. You will see detailed logs from the `WorkflowDriver` as it executes the autonomous loop, including task selection, planning, agent execution, validation results, and roadmap status updates.
5.  **Review Outputs:** After the autonomous loop iteration completes (indicated by logs), check the updated `ROADMAP.json`, any generated/modified code files, and the API server logs for the detailed Grade Report and workflow status. Address any tasks marked "Blocked" or issues highlighted in the report manually before initiating the workflow again (by running the CLI command again).

For a detailed explanation of the autonomous workflow, including the structure of `ROADMAP.json` and the Driver's internal process, please refer to the [Full Markdown-Only Automation Workflow Guide](docs/workflows/markdown_automation.md).

## <a name="workflow-use-case-example"></a>Workflow and Use Case Example

The Metamorphic Software Genesis Ecosystem aims to automate software development from specification to deployment. Consider generating software for an **Autonomous Drone Package Delivery System**. This example showcases the framework's ability to handle complexity, security, ethics, and hardware interaction.

**Conceptual Workflow (Post-Phase 1.6 - Automated):**

1.  **Initiation:** User initiates the automated workflow via the CLI (`python src/cli/main.py`). The CLI automatically gathers context (specs, policies, documentation) and submits it to the Driver LLM API endpoint (`/genesis/drive_workflow`).
2.  **Autonomous Workflow Execution (Driver LLM Loop):** The Driver LLM, triggered by the API call, autonomously:
    *   Selects the next task from `ROADMAP.json`.
    *   Generates a step-by-step solution plan for the task.
    *   Iterates through the plan steps, automatically invoking relevant agents (like the Coder LLM for code generation) and tools (like `write_file`) as needed by the plan.
3.  **Automated Validation (Iterative Loop - Orchestrated and Executed by Driver):** As part of the plan execution, the Driver orchestrates and *automatically executes* validation steps on generated/modified code artifacts. This includes:
    *   Code Quality (`CodeReviewAgent` - Flake8, Bandit).
    *   Security Scans (`SecurityAgent` - ZAP).
    *   Testing (`TestGenAgent` - basic, *automatically run via pytest*).
    *   Ethical Assessment (`EthicalGovernanceEngine`).
    *   Formal Verification (`FormalVerificationEngine` - future).
    *   Validation results are captured, logged, and feed into the Grade Report.
4.  **Automated Feedback & Roadmap Update:** The Driver automatically parses the Grade Report, determines the outcome based on predefined criteria (e.g., test pass rate, severity of issues), and *automatically updates the task status in `ROADMAP.json`*.
5.  **Integration:** Validated code is written to the filesystem via the `write_file` tool, orchestrated by the Driver.
6.  **Improvement:** `ContinuousLearningCore` analyzes performance and feedback to refine agents and processes (future).
7.  **User Review & Intervention:** The user monitors the API server logs and reviews the outputs of the autonomous iteration (generated code, updated roadmap, reports, logs) to monitor progress and intervene if necessary (e.g., if a task is marked 'Blocked' or requires manual design decisions).

    *(For full details on the automated workflow and the iterative grading process, see [**docs/workflows/markdown_automation.md**](docs/workflows/markdown_automation.md) and [**CONTRIBUTING.md - Contribution Review Process: Iterative Probability-Based Grading**](CONTRIBUTING.md#contribution-review-process-iterative-probability-based-grading)).*

    **With the completion of Phase 1.6, the Metamorphic Core now orchestrates the entire development iteration autonomously, from initiation via CLI/API through validation execution, grade report parsing, and roadmap status updates. The user's role shifts from manual step execution to initiating the loop and reviewing the results.**

*   **Key Components (Detailed):**
    *   **Human Input & Oversight Interface:** (Planned Web UI) Secure portal for spec submission (text, later diagrams), configuration, feedback, ethical guidance input, ERB overrides, progress dashboards. The CLI (`src/cli/main.py`) now serves as the primary *initiation* interface for the automated workflow. **This CLI now calls the `/genesis/drive_workflow` API endpoint to trigger the autonomous loop.**
    *   **Metamorphic Core (Adaptive AI Orchestration):**
        *   *Dynamic Knowledge Graph:* Neo4j or similar graph DB storing nodes (code chunks, specs, policies, vulnerabilities, tests, metrics) and semantic relationships. Enables complex querying for context retrieval and pattern analysis. (Phase 2 Iteration 2 focuses on expanding the KG schema to store richer code semantics).
        *   *Intelligent LLM Orchestration Layer:* Manages API calls to multiple LLMs (Gemini, Hugging Face, potentially OpenAI). Implements context window management (semantic chunking, summarization), cost/latency optimization (model selection based on task complexity), robust retries, and failover logic. Uses `TokenAllocator` for budget management. **This layer is now orchestrated by the autonomous Driver LLM, triggered via the `/genesis/drive_workflow` API endpoint.**
        *   *Modular AI Agent Network:*
            *   `SpecificationAnalysisAgent`: Parses natural language/structured input into formal requirements, potentially using AST analysis and LLMs.
            *   `TestGenerationAgent`: Generates pytest tests (placeholders in MVP, meaningful tests including HIL using code/spec analysis later). **Automated execution of these tests is now part of the Phase 1.6 workflow.** (Phase 2 Iteration 2 focuses on enhancing this agent for more intelligent test generation).
            *   `CodeGenerationAgent`: (Post-MVP) Generates code (Python, Go, Rust, JS/TS, C++) based on specs from KG/LLM Orchestrator.
            *   `CodeReviewAgent`: Runs static analysis with **Flake8** for code quality and **Bandit** for security. **Integrated into `/genesis/analyze-ethical` API endpoint. Automated execution is now part of the Phase 1.6 workflow.** (Phase 2 Iteration 2 focuses on enhancing this agent with semantic analysis).
            *   `SecurityAgent`: Orchestrates security tools (ZAP DAST now; SAST via Bandit/Semgrep later). Analyzes results, stores findings in KG. **Automated execution of relevant checks is now part of the Phase 1.6 workflow.**
            *   `PerformanceAnalysisAgent`: (Post-MVP) Integrates profiling tools (cProfile) and analyzes performance metrics.
            *   `FormalVerificationEngine`: Interfaces with Coq (proofs compiled in CI), Isabelle/HOL, and Z3 (SMT solver) for multi-layered verification.
            *   `PredictiveRiskAssessmentModule`: Uses `QuantumRiskPredictor` (trained on historical KG data) to forecast ethical/security risks.
            *   `SelfMonitoringAndAdaptiveHealing`: Monitors system metrics (Prometheus), logs errors, triggers recovery actions.
            *   `ResourceManagementOptimization`: (Post-MVP) Optimizes cloud resource usage, potentially using Kubernetes HPA based on Prometheus metrics.
    *   **Ethical Governance Framework:**
        *   **Project Process Ethics:** Extend the Ethical Governance Framework to evaluate and guide MSGE's own development processes, ensuring they align with ethical principles of **transparency, risk mitigation, and continuous improvement**. This includes using AI-driven roadmap refinement to minimize uncertainty and enhance project success probability, and proactively addressing potential ethical concerns within the development process itself. **Furthermore, to ensure consistent ethical considerations in code contributions, we employ an **Iterative Grading Process** (detailed in [CONTRIBUTING.md - Contribution Review Process: Iterative Probability-Based Grading](CONTRIBUTING.md#contribution-review-process-iterative-probability-based-grading)) that includes "Ethical Policy Compliance Probability", "Code Style Compliance Probability", and other key quality metrics in code reviews and iterative refinement cycles.**
         *   *EthicalPolicyEngine (`EthicalGovernanceEngine`):* Loads JSON policies (`jsonschema` validation). `enforce_policy` method checks code/metadata against loaded constraints (regex, keyword checks, **AST analysis for transparency**). Returns compliance status. **Automated execution of policy enforcement is now part of the Phase 1.6 workflow.**
         *   *BiasDetectionMitigationModule:* Uses NLP libraries (spaCy, Transformers) or fairness toolkits (Fairlearn) to analyze text (comments, docs) and potentially code structure for bias indicators. (Post-MVP) Implements mitigation strategies (e.g., suggesting alternative phrasing).
         *   *TransparencyExplainabilityModule:* (Planned) Provides API endpoints to retrieve justification for policy violations or agent decisions, potentially querying LLM logs or KG links.
    *   **Formal Verification & Resilience Subsystem:**
        *   *FormalVerificationEngine:* Interfaces with Coq (proofs compiled in CI), Isabelle/HOL, and Z3 (SMT solver) for multi-layered verification.
        *   *QuantumStatePreserver:* (MVP placeholder) Saves quantum states for auditability.
        *   *SelfMonitoringAndAdaptiveHealing:* Prometheus metrics, anomaly detection (post-MVP).
    *   **Continuous Learning & Improvement Loop:**
        *   *PerformanceAnalysisAgent:* (Post-MVP) Benchmarking, profiling, bottleneck analysis.
        *   *ContinuousLearningCore:* ML-driven process adaptation.
        *   *FeedbackCaptureModule:* API endpoints for user feedback.

**III. Technical Specifications & KPIs (Initial)**

### **Expected Phase Improvements**

The following table summarizes the anticipated cumulative improvements in key areas for each phase of the Metamorphic Software Genesis Ecosystem. Note that these are ballpark estimates and are subject to change.

| Feature                           | Phase 1.5 (Workflow Automation) | Phase 1.6 (Enhanced Automation) | Phase 2 (Enhanced Intelligence) | Phase 3 (Cyber-Physical Systems) | Phase 4 (Quantum) | Phase 5 (Sustaining) |
| --------------------------------- | ------------- | ------------------------------- | ------------------------------- | ------------------------------- | --------------- | -------------------- |
| Development Efficiency/Speed      | 5-10%         | 15-25%                          | 30-40%                          | 40-55%                          | 50-70%          | 60-80%              |
| Software Quality (Bugs/Vulnerabilities) | 5-10%         | 10-15%                          | 30-40%                          | 50-70%                          | 70-90%          | 80-98%              |
| Ethical Compliance                | 10-20%        | 25-35%                          | 40-60%                          | 60-80%                          | 80-95%          | 90-99%              |
| Resource Efficiency               | Negligible    | Negligible                      | 5-10%                           | 15-25%                          | 20-35%          | 30-45%              |

**Important Notes:**

*   All percentages are cumulative.
*   These are "ballpark" estimates only and are subject to significant uncertainty.
*   Actual improvements will depend on successful implementation, domain specificity, data availability, and human factors.

*   **Core Tech Stack:** Python (primary), Go (concurrency/API), Rust (safety-critical), JavaScript/TypeScript (UI - planned), Coq/Isabelle/Z3 (formal methods).
*   **LLM Providers:** Gemini (default in MVP), Hugging Face (via `InferenceClient`, OpenAI (future).
*   **Knowledge Graph:** Neo4j (planned), initially in-memory Python dict for MVP.
*   **Security Scanning:** OWASP ZAP (DAST - integrated in CI for MVP), Bandit, Semgrep (SAST - post-MVP).
*   **Testing Frameworks:** pytest (unit, integration), Hypothesis (property-based).
*   **CI/CD:** GitHub Actions (MVP), GitLab CI/CD (future option).
*   **Monitoring & Telemetry:** Prometheus (planned), basic logging in MVP.
*   **Ethical Policy Format:** JSON, schema-validated (`ethical_policy_schema.json`).
*   **Formal Specification Language:** Natural language (constraints), Coq/Isabelle/Z3 (formal proofs).

**V. Future Evolution (Beyond Version 1.0):**

*(Roadmap for future phases - examples)*

*   **Phase 1.6 (Enhanced Workflow Automation):** **Completed** - Completed the end-to-end automation layer.
*   **Phase 2 Iteration 2 (Enhanced Agents & Knowledge Graph):** Current focus - Advanced AI planning, reinforcement learning for agent optimization, deeper KG integration, semantic code search, AI-driven debugging/refactoring. (Phase 2 Iteration 2 will be the first iteration focusing on agent and KG enhancements).
*   **Phase 2 Iteration 3 (Ethical Governance & API Expansion):** Deepen ethical governance integration, expand API endpoints for broader functionality and external integration.
*   **Phase 3 (Cyber-Physical Systems Focus):** Integration with robotics frameworks (ROS 2), hardware-in-the-loop (HIL) testing, formal verification of safety-critical embedded code, real-time ethical monitoring for autonomous systems.
*   **Phase 4 (Quantum-Augmented Genesis):** Full integration of quantum computing for optimization, risk prediction, and potentially code generation, quantum-resistant security measures.

---

**VI. Phase 5: Sustaining - Continuous Improvement & Evolution**

*Goal:* To ensure the long-term viability, security, ethical alignment, and performance of the Metamorphic Software Genesis Ecosystem through continuous monitoring, automated analysis, and community-driven contributions.

*Key Principles:*

    *   **Data-Driven Evolution:** Base all improvements on measurable KPIs and empirical data, leveraging telemetry and user feedback.
    *   **Proactive Threat Mitigation:** Continuously monitor for emerging security threats and ethical risks, implementing proactive countermeasures.

---

## <a name="core-api-endpoints"></a>Core API Endpoints

The Metamorphic Core exposes several API endpoints for interacting with its functionality. The primary endpoint for driving the automated workflow is `/genesis/drive_workflow`.

*   `/genesis/health` (GET): Checks the health of the API server and core components.
*   `/genesis/analyze-ethical` (POST): Analyzes provided code for ethical compliance and code quality based on a specified or default policy.
*   `/genesis/drive_workflow` (POST): Initiates the autonomous workflow loop managed by the WorkflowDriver. Requires `roadmap_path` and `output_dir` in the request body. **This endpoint is typically called by the CLI (`src/cli/main.py`).**

*(More endpoints will be added in future phases)*

## <a name="contributing"></a>Contributing

We enthusiastically welcome contributions to the Metamorphic Software Genesis Ecosystem! Please see the [CONTRIBUTING.md](CONTRIBUTING.md) file for detailed guidelines on how to contribute, including setting up your development environment and understanding the automated workflow.

## <a name="further-documentation"></a>Further Documentation

*   [SPECIFICATION.md](SPECIFICATION.md): Full high-level specification and detailed vision.
*   [CONTRIBUTING.md](CONTRIBUTING.md): Guidelines for contributing to the project.
*   [ROADMAP.md](ROADMAP.md): The project's development roadmap (automatically generated from ROADMAP.json).
*   [docs/workflows/markdown_automation.md](docs/workflows/markdown_automation.md): Detailed guide to the Automated Workflow (Markdown-Only Automation).
*   [COMPETITIVE_LANDSCAPE.md](COMPETITIVE_LANDSCAPE.md): Analysis of the competitive landscape.
*   [INSTALL.md](INSTALL.md): Basic installation instructions (referencing this README).

## <a name="troubleshooting"></a>Troubleshooting

*   **Docker Compose Issues:** Ensure Docker Desktop is running. Check container logs (`docker logs <container_name>`). Verify port conflicts.
*   **API Key Errors:** Double-check your `.env` file and ensure required keys are set correctly and match the expected format.
*   **LLM Connection Errors:** Verify your internet connection and check the status of the LLM provider's API.
*   **Workflow Driver Errors:** Monitor the API server logs (`python src/api/server.py`) for detailed error messages and tracebacks. Check the generated Grade Report for validation failures.
*   **Path Issues:** Ensure paths provided to the CLI or API are correct relative to the project root and that the API server has necessary file permissions.

## <a name="license"></a>License

This project is licensed under the AGPLv3 License - see the [LICENSE](LICENSE) file for details.

## <a name="contact"></a>Contact

For questions, feedback, or collaboration inquiries, please open an issue on the GitHub repository or reach out via [specify contact method, e.g., email, Discord, etc.].

## <a name="Disclaimer"></a>Disclaimer

This is an experimental project leveraging advanced AI models. Generated code may contain errors, security vulnerabilities, or ethical issues. Always review and verify generated outputs before deployment. The project is under active development, and APIs/features may change.