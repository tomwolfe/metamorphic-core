# Metamorphic Software Genesis Ecosystem

[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-AGPLv3-blue.svg)](LICENSE)
[![Roadmap Status](https://img.shields.io/badge/Roadmap-Phase_2.2_IN_PROGRESS-blue)](ROADMAP.md)

**🎯 CURRENT FOCUS: PHASE 2 ITERATION 2 - Enhanced Agents & Knowledge Graph 🚀**

Phase 1 MVP is complete, and **Phase 1.5: Workflow Automation is now also complete!** We successfully implemented the Markdown-Only Automation Workflow, achieving autonomous execution of development tasks (task selection, planning, agent invocation, file writing) once the Driver LLM is initiated. We are now transitioning into **Phase 2 Iteration 2**, focusing on enhancing the core AI agents and deepening their integration with the Knowledge Graph to improve intelligence, context handling, and overall system performance. See the [Roadmap](#further-documentation) for details.

---

**Strategic Impact of Phase 1.5:**

Phase 1.5 focused on implementing a Markdown-Only Automation Workflow to enhance the efficiency and consistency of our development process. **With the successful completion of Phase 1.5 Stage 3, we have achieved a robust foundation for significant acceleration and improved quality in later phases by automating the core Driver LLM loop.** This focus on refining our *own* development processes aligns with our core ethical principles of transparency, continuous improvement, and efficient resource utilization. This also supports more robust and reliable AI-driven code generation and validation.

**Three-Stage Approach to Markdown-Only Automation (Completed):**

Phase 1.5 was implemented in three key stages. Stage 1 established the fundamental markdown automation workflow and CLI driver. Stage 2 enhanced the workflow driver with key functionalities like secure file handling, automated Coder LLM invocation, automated `write_file` tool execution, LLM prompt generation and integration, and well-defined, actionable steps. **Stage 3 successfully achieved full Driver loop automation, enabling the Driver LLM to autonomously select tasks, generate plans, invoke agents, and manage files based on the roadmap.**

**Estimated Potential Benefits (Long-Term, Full Integration):**

*   **MSGE (Without Phase 1.5):** Represents a baseline system with manual operations and loosely coupled components, delivering a starting-point project success likelihood of 65%.
*   **Phase 1.5 (Completed):** Successfully automated key routine workflow operations (task processing, agent invocation, file writing), improving developer experience by an estimated 85% in those specific tasks once fully integrated.
*   **MSGE (With Phase 1.5):** The long-term objective is a fully integrated system achieving up to a 95% grade in overall developer efficiency. Faster iteration cycles and more consistent code quality are expected. Successful execution of the Markdown-Only Automation Workflow is intended to enhance adherence to evolving ethical standards.

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
    *   [Quickstart Guide to Markdown-Only Automation](#quickstart-guide-to-markdown-only-automation)
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

The Metamorphic Software Genesis Ecosystem is an AI-driven framework designed to autonomously generate, maintain, and evolve secure, ethical, and high-performance software solutions from high-level specifications. It continuously refines its capabilities through feedback and self-improvement. **A key strategic decision was the implementation of Phase 1.5, which is now complete.** Phase 1.5 focused on improving the *development process itself* by implementing a Markdown-Only Automation Workflow. **With the successful completion of Phase 1.5 Stage 3, the core Driver LLM loop is now automated, enabling autonomous task selection, planning, agent invocation, and file writing.** This is aimed at faster testing, rapid prototyping and easier iterative grading, and will amplify the value and efficiency of the overall system. We are now focused on **Phase 2 Iteration 2: Enhanced Agents & Knowledge Graph**, improving the intelligence of our core AI agents and deepening their integration with the Knowledge Graph.

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
*   **Docker:** Docker Desktop (optional, for Redis/ZAP). See [Troubleshooting](#troubleshooting) for Docker issues.
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
    pip install -r requirements/dev.txt # For Flake8 code quality checks
    ```
7.  **Install Pre-commit Hooks (Optional, Recommended):**
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

### <a name="quickstart-guide-to-markdown-only-automation"></a>Quickstart Guide to Markdown-Only Automation

For a streamlined, AI-driven development experience, you can use the **"Markdown-Only Automation" workflow**. This workflow leverages the "Ideal Self-Driving Prompt" and augmented `.md` documentation to guide an LLM to autonomously drive development tasks. **With the successful completion of Phase 1.5 Stage 3, the core Driver LLM loop is now automated, including task selection, solution planning, automated Coder LLM invocation, automated `write_file` tool execution, and iterative processing of plan steps.**

**(As of Phase 1.5 Stage 3, the Driver LLM now automatically selects tasks, generates plans, invokes the Coder LLM, and uses the `write_file` tool based on the plan. The manual copy-pasting of Coder LLM output is no longer required for code generation. The primary remaining manual step is the initial construction and submission of the comprehensive prompt to the Driver LLM API endpoint. Automating this step is a key task in Phase 2 Iteration 2.)**

**Quickstart Steps (Post-Phase 1.5 Stage 3):**

1.  **Prepare your `ROADMAP.json` and codebase text** as described in the [Full Guide](docs/workflows/markdown_automation.md). The roadmap is now managed in `ROADMAP.json`, not `ROADMAP.md`.
2.  **Open your terminal** in the `metamorphic-core` project directory.
3.  **Run the CLI to initiate the workflow driver:**

    ```bash
    python src/cli/main.py
    ```
    (You can optionally specify a different roadmap file or output directory using `--roadmap` and `--output-dir` arguments as described in the [Full Markdown-Only Automation Workflow Guide](docs/workflows/markdown_automation.md#cli-integration-and-execution)).
4.  **Copy the "Ready-to-Use "Ideal" Self-Driving Prompt"** from [docs/workflows/markdown_automation.md](docs/workflows/markdown_automation.md).
5.  **Paste the prompt into your LLM interface (this is the Driver LLM).**
6.  **Replace the `[PASTE_..._HERE]` placeholders** in the prompt with the *content* of the respective files (`SPECIFICATION.md`, `ROADMAP.md`, `CONTRIBUTING.md`, `docs/workflows/markdown_automation.md`, `COMPETITIVE_LANDSCAPE.md`).
7.  **Submit the prompt to the Driver LLM.**
8.  **Review the Driver LLM's output.** It will now autonomously select a task, generate a plan, execute the plan steps (including invoking the Coder LLM and writing files), and provide a Grade Report for the completed iteration.
9.  **Follow the User Actionable Steps.** These steps will guide you through reviewing the AI's work, running tests, and updating the roadmap status manually (until roadmap automation is implemented).
10. **Provide feedback** to the Driver LLM using one of the specified letter codes (e.g., `A: Confirm` if the steps were completed successfully and the outcome is satisfactory).

**Example Quickstart Scenario:**

Let's assume you want to work on **Task ID: task_2_2a** (Automate Initial Prompt Submission from CLI) from your `ROADMAP.json`.

1.  **Open a terminal** in your `metamorphic-core` project directory.
2.  **Run the CLI:**

    ```bash
    python src/cli/main.py
    ```

3.  **Review the CLI output.** It should indicate that "Task ID: task_2_2a" is selected (if it's the first 'Not Started' task in your `ROADMAP.json`). The output will look similar to this:

    ```text
    Using roadmap: /path/to/metamorphic-core/ROADMAP.json
    Using output directory: /path/to/metamorphic-core/output
    Next task selected: ID=task_2_2a, Name=Automate Initial Prompt Submission from CLI
    ```

4.  **Copy the "Ready-to-Use "Ideal" Self-Driving Prompt"** from `docs/workflows/markdown_automation.md`.
5.  **Paste the prompt into your LLM interface (Driver LLM).**
6.  **Replace the `[PASTE_..._HERE]` placeholders** in the prompt with the *content* of the respective files (`SPECIFICATION.md`, `ROADMAP.md`, `CONTRIBUTING.md`, `docs/workflows/markdown_automation.md`, `COMPETITIVE_LANDSCAPE.md`).
7.  **Submit the prompt to the Driver LLM.**
8.  **Review the Driver LLM's output.** It will provide a solution plan for `task_2_2a`, autonomously execute the steps (e.g., generating code for the CLI modification, writing the file), and provide a Grade Report.
9.  **Follow the User Actionable Steps.** These steps will guide you through reviewing the generated code, running tests for the CLI, and manually updating the roadmap status for `task_2_2a`.
10. **Provide feedback** to the Driver LLM using one of the specified letter codes (e.g., `A: Confirm` if the review is satisfactory and steps are complete).

**For detailed instructions and the full "Ideal Self-Driving Prompt" text, please refer to the [Full Markdown-Only Automation Workflow Guide](docs/workflows/markdown_automation.md).** Note that the `ROADMAP.md` file is now autogenerated from `ROADMAP.json`.

## <a name="workflow-use-case-example"></a>Workflow and Use Case Example

The Metamorphic Software Genesis Ecosystem aims to automate software development from specification to deployment. Consider generating software for an **Autonomous Drone Package Delivery System**. This example showcases the framework's ability to handle complexity, security, ethics, and hardware interaction.

**Conceptual Workflow (Post-Phase 1.5 Stage 3):**

1.  **Input:** Provide a high-level software description and detailed ethical policies/constraints (via initial prompt to Driver LLM).

    *   Example Spec: "Develop software for a drone delivery system..."
    *   Policy Files (JSON): `safety_policy.json`, `privacy_policy.json`, `security_policy.json`
2.  **Autonomous Workflow Execution (Driver LLM Loop):** The Driver LLM, initiated by the user's prompt, autonomously:
    *   Selects the next task from `ROADMAP.json`.
    *   Generates a step-by-step solution plan for the task.
    *   Iterates through the plan steps, automatically invoking relevant agents (like the Coder LLM) and tools (like `write_file`) as needed by the plan.
3.  **Validation (Iterative Loop - Orchestrated by Driver):** The Driver orchestrates validation steps as part of the plan execution. This includes:
    *   Code Quality (`CodeReviewAgent` - Flake8).
    *   Security Scans (`SecurityAgent` - ZAP).
    *   Testing (`TestGenAgent` - placeholder/basic).
    *   Ethical Assessment (`EthicalGovernanceEngine`).
    *   Formal Verification (`FormalVerificationEngine` - future).
    *   Validation results drive further steps in the plan (e.g., generating a fix if validation fails).
4.  **Integration:** Validated code is written to the filesystem via the `write_file` tool, orchestrated by the Driver.
5.  **Improvement:** `ContinuousLearningCore` analyzes performance and feedback to refine agents and processes (future).
6.  **User Review & Feedback:** The user reviews the outputs of the autonomous iteration (generated code, reports, logs) and provides feedback to the Driver LLM to guide the next iteration or handle issues.

**End Products:**

*   Ready-to-deploy software (Cloud Backend, ESP32 Firmware).
*   Comprehensive test suites (including Hardware-in-the-Loop).
*   Configuration/policy files.
*   Formal verification artifacts.
*   MSGE Reports: Ethical Compliance, Security Analysis, Test Coverage, Formal Verification.

## <a name="core-api-endpoints"></a>Core API Endpoints

*(Focus on MVP - see [API Documentation](docs/api/api-endpoints.md) for future plans)*

| Endpoint                        | Method | Description                                                                       | Status (MVP)     |
| :---------------------------- | :----- | :------------------------------------------------------------------------------ | :--------------- |
| `/genesis/health`             | GET    | Check API server status. Returns `{"status": "ready"}`.                         | ✅ Working       |
| `/genesis/analyze-ethical`    | POST   | Analyzes Python code: Configurable Ethics, **Flake8 Quality**, Placeholder Tests. | ✅ MVP Core (Quality) |
| `/genesis/solve-math`         | POST   | Basic LLM integration test endpoint.                                            | ✅ Working (Test) |
| `/genesis/ethical/audit/{state_id}`   | GET    | Retrieve audit trail data (planned).                                            | ❌ Not Implemented |
| `/genesis/ethical/visualize/{state_id}` | GET    | Obtain visualization data (planned).                                      | ❌ Not Implemented |
| `/genesis/drive_workflow`     | POST   | Initiates the autonomous Workflow Driver loop (Planned for Phase 2 Iteration 2). | ❌ Not Implemented |

**Sample MVP Request/Response - `/genesis/analyze-ethical`:**

[Example curl request and JSON response for `/genesis/analyze-ethical` - as in the original README]

## <a name="contributing"></a>Contributing

Contributions are welcome! Please align with the current [Phase 2 Iteration 2 focus](ROADMAP.md) and see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines (basic guidelines currently, enhanced guidelines planned for Phase 2 Iteration 2).

## <a name="further-documentation"></a>Further Documentation

*   **[Full High-Level Specification (Detailed Vision)](SPECIFICATION.md)**
*   **[Development Roadmap (MVP & Beyond)](ROADMAP.md)** - *Note: This file is autogenerated from `ROADMAP.json`. Do not edit directly!*
*   **[Competitive Landscape Analysis](COMPETITIVE_LANDSCAPE.md)**
*   **[API Documentation (Placeholder - In Progress)](docs/api/api-endpoints.md)** - *Detailed API documentation for the `/genesis/analyze-ethical` endpoint will be available here by the end of Phase 2 Iteration 1 (Week 9).*
*   **[Contribution Guidelines](CONTRIBUTING.md)**
*   **[Full Markdown-Only Automation Workflow Guide](docs/workflows/markdown_automation.md)** **(UPDATED - Recommended for streamlined AI-driven development)**

## <a name="troubleshooting"></a>Troubleshooting

### LLM API Key Errors

*   **Verify API Keys in `.env`:** Ensure API keys are correct in `.env`.
*   **Check `LLM_PROVIDER`:** Verify `LLM_PROVIDER` is set correctly in `.env` (`gemini` or `huggingface`).
*   **Key Validity:** Check API key validity in your provider's console.
*   **Typographical Errors:** Double-check for typos in `.env`.

### Docker Compose Issues (Redis/ZAP)

*   **Ensure Docker Desktop is Running:** Verify Docker Desktop is running.
*   **Check Container Status:** Use `docker ps` to check container status. Use `docker-compose logs redis` or `docker-compose logs zap` for errors.
*   **Port Conflicts:** Check for port conflicts (`docker ps -a`).
*   **`docker-compose.yml` Existence:** Ensure `docker-compose.yml` exists in the project root.
*   **Restart Docker:** Try restarting Docker Desktop.

### Python Dependency Errors

*   **Verify Python Version:** `python --version` (must be 3.11+).
*   **Virtual Environment Activation:** Ensure `venv` is activated (`(venv)` in prompt).
*   **Upgrade pip:** `pip install --upgrade pip`.
*   **Re-install Dependencies:** `pip install -r requirements/base.txt` and `pip install -r requirements/dev.txt`.
*   **`flake8` Installation:** Verify `flake8` is installed (`pip install -r requirements/dev.txt`).
*   **Cache Issues:** `pip cache purge` and reinstall dependencies.

### API Connection Errors

*   **Flask Server Running:** Run `python src/api/server.py`.
*   **Host and Port:** Check server address (`http://127.0.0.1:5000`).
*   **Docker Container Ports:** Verify port mappings in `docker-compose.yml` (5000:5000).
*   **Firewall:** Check firewall rules blocking port 5000.

### Ethical Policy Errors

*   **Policy File Existence:** Ensure policy files (`.json`) are in `policies/`.
*   **File Paths:** Verify file paths in `src/api/routes/ethical_endpoints.py`.
*   **JSON Syntax:** Validate policy files for correct JSON.
*   **Schema Compliance:** Ensure policies match `ethical_policy_schema.json`.

### Code Quality Issues Not Reported

*   **`flake8` Installation:** Verify `flake8` is installed (`pip install -r requirements/dev.txt`).
*   **Server Logs:** Check Flask server logs for `CodeReviewAgent` or `flake8` errors.
*   **API Response Structure:** Verify `code_quality` section in API response JSON.
*   **Flake8 Executable Path:** Ensure `flake8` is in your system's PATH or venv's `bin`.

### Known Issues

#### ZAP Service (Local `docker-compose.yml`) Issue

*   **Local ZAP Unreliable in MVP:** Local ZAP service in `docker-compose.yml` may not be reliable for local security scans in this MVP release.
*   **CI Pipeline ZAP Scans Reliable:** Rely on ZAP Baseline Scan reports in CI pipeline runs for security vulnerability assessments.
*   **Local ZAP Scans Not Reliable for MVP:** Local ZAP scans via `docker-compose up` are not currently reliable.
*   **Resolution Planned Post-MVP:** Resolution for local ZAP service is planned for a future release.
*   **Note:** Code quality reporting via Flake8 is verified and functional for both local and CI pipeline use.

## <a name="license"></a>License

This project is licensed under the GNU Affero General Public License v3.0 (AGPLv3). See the `LICENSE` file for details. Aligned with OECD AI Principles and supports GDPR/Brexit compliance goals.

## <a name="contact"></a>Contact

tomwolfe@gmail.com

## <a name="disclaimer"></a>Disclaimer

Disclaimer: The Metamorphic Software Genesis Ecosystem is provided "as is", without warranty of any kind, express or implied, including but not limited to the warranties of merchantability, fitness for a particular purpose and noninfringement. In no event shall the authors or copyright holders be liable for any claim, damages or other liability, whether in an action of contract, tort or otherwise, arising from, out of or in connection with the software or the use or other dealings in the software.  This software is for research and development purposes only and should not be used for production systems without extensive testing and validation.  Ethical considerations and security best practices are paramount.  Use with caution and at your own risk.