# Metamorphic Software Genesis Ecosystem

[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-AGPLv3-blue.svg)](LICENSE)
[![Roadmap Status](https://img.shields.io/badge/Roadmap-Phase_1.5_Workflow_Automation_Focus-yellow)](ROADMAP.md)
[![Roadmap Status](https://img.shields.io/badge/Roadmap-Phase_1.5_Workflow_Automation_Focus-yellow)](ROADMAP.md)  <-- UPDATED BADGE TEXT

**🎯 CURRENT FOCUS: PHASE 1.5 - Workflow Automation Side Project (Weeks 7-8) - PRIORITIZED TO SIGNIFICANTLY ACCELERATE FUTURE DEVELOPMENT 🚀**

Phase 1 MVP is complete! We are now prioritizing **Phase 1.5: Workflow Automation Side Project** to streamline and accelerate development for Phase 2 and beyond. See the [Roadmap](#further-documentation) for details.

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

The Metamorphic Software Genesis Ecosystem is an AI-driven framework designed to autonomously generate, maintain, and evolve secure, ethical, and high-performance software solutions from high-level specifications.  It continuously refines its capabilities through feedback and self-improvement.

**Key Objectives:**

-   **Autonomous Generation:**  Create functional applications from natural language or structured specifications.
-   **Ethical Governance:**  Enforce configurable ethical policies throughout development.
-   **Automated Quality & Security:**  Integrate continuous testing, code review, and formal verification.
-   **Self-Improving Development Process:**  Optimize its own development using AI-driven planning.
-   **Self-Improvement:**  Learn from analysis, feedback, and metrics to enhance its core capabilities.

*(For the full detailed vision and architecture, see [**SPECIFICATION.md**](SPECIFICATION.md))*

## <a name="getting-started"></a>Getting Started

### <a name="prerequisites"></a>Prerequisites

-   **Python Version:** Python 3.11+. Verify with `python --version`.
-   **Docker:** Docker Desktop (optional, for Redis/ZAP). See [Troubleshooting](#troubleshooting) for Docker issues.
-   **API Keys:** Required API keys (see [.env Configuration & API Keys](#env-configuration-api-keys)).
-   **Git:** Git installed on your system.

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
    -   Edit `.env` and set `GEMINI_API_KEY=your_gemini_api_key` with your Gemini API key from [Google AI Studio](https://ai.google.dev/). **This is required for the core functionality.**
3.  **Configure Optional API Keys (in `.env`):**
    -   `HUGGING_FACE_API_KEY`: For Hugging Face models (from [Hugging Face](https://huggingface.co/settings/tokens)).
    -   `YOUR_GITHUB_API_KEY`: For future GitHub integrations (from [GitHub](https://github.com/settings/tokens)).
    -   `ZAP_API_KEY`: For local ZAP security scans (advanced, optional) - default is `changeme`.
4.  **Optional Settings (in `.env`):**
    -   `LLM_PROVIDER`, `LLM_MAX_RETRIES`, `LLM_TIMEOUT`, `HUGGING_FACE_MODEL`, `DOCKERHUB_USERNAME` (see `.env.example` for details).
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

-   **Operating System:** Linux (Ubuntu recommended), macOS, Windows (Windows 10/11 tested).
-   **Python Version:** Python 3.11+ (required).
-   **Docker:** Optional (recommended for services). See [Troubleshooting](#troubleshooting) for Docker issues.
-   **RAM:** 8GB RAM minimum, 16GB+ recommended for LLM features.
-   **Disk Space:** 2GB free disk space or more.

### <a name="quickstart-guide-to-markdown-only-automation"></a>Quickstart Guide to Markdown-Only Automation

For a streamlined, AI-driven development experience with minimal manual prompting, you can use the **"Markdown-Only Automation" workflow**. This workflow leverages the "Ideal Self-Driving Prompt" and the augmented `.md` documentation to guide an LLM to autonomously drive development tasks.

**Quickstart Steps:**

1.  **Prepare your `.md` files and codebase text** as described in the [Full Guide](docs/workflows/markdown_automation.md).
2.  **Copy the "Ready-to-Use "Ideal" Self-Driving Prompt"** from [docs/workflows/markdown_automation.md](docs/workflows/markdown_automation.md).
3.  **Paste the prompt into your LLM interface, replacing the placeholders** with your codebase and `.md` file content.
4.  **Review the LLM's output, implement "User Actionable Steps," and provide confirmation** to proceed to the next task. **When providing confirmation, use one of the following options, formatted as described in `docs/workflows/markdown_automation.md`:**
    *   **`A: [Optional message if all tests passed, and implementing changes]`**
    *   **`B: [Detailed test output showing failing tests]`**
    *   **`C: [Missing File(s): list of missing files]`**
    *   **`D: [Your question to the LLM]`**
    *   **`E: [Describe a code issue you've found]`**
    *   **`F: [Reason for regenerating, e.g., 'Tests are too basic' or 'Code is inefficient']`**

**For detailed instructions and the full "Ideal Self-Driving Prompt" text, please refer to the [Full Markdown-Only Automation Workflow Guide](docs/workflows/markdown_automation.md).**

## <a name="workflow-use-case-example"></a>Workflow and Use Case Example

The Metamorphic Software Genesis Ecosystem aims to automate software development from specification to deployment.  Consider generating software for an **Autonomous Drone Package Delivery System**. This example showcases the framework's ability to handle complexity, security, ethics, and hardware interaction.

**Conceptual Workflow:**

1.  **Input:** Provide a high-level software description and detailed ethical policies/constraints.
    *   Example Spec: "Develop software for a drone delivery system..."
    *   Policy Files (JSON): `safety_policy.json`, `privacy_policy.json`, `security_policy.json`
2.  **Refinement:** AI clarifies requirements using the `SpecificationAnalysisAgent`.
3.  **Design:** AI generates a software architecture, stored in the Knowledge Graph (KG).
4.  **Generation:** `CodeGenerationAgent` creates code (Python, Go, etc.) using LLMs orchestrated by `LLMOrchestrator`.
5.  **Validation (Iterative Loop):**
    -   **Checks:** Code Quality (`CodeReviewAgent` - Flake8), Ethical Assessment (`EthicalGovernanceEngine`), Security Scans (`SecurityAgent`), Testing (`TestGenAgent`), Formal Verification (`FormalVerificationEngine`).
    -   **Feedback & Regeneration:** Validation results drive code regeneration until all checks pass.
6.  **Integration:** Validated code is integrated via Git and CI/CD pipelines.
7.  **Improvement:** `ContinuousLearningCore` analyzes performance and feedback to refine agents and processes.

**End Products:**

-   Ready-to-deploy software (Cloud Backend, ESP32 Firmware).
-   Comprehensive test suites (including Hardware-in-the-Loop).
-   Configuration/policy files.
-   Formal verification artifacts.
-   MSGE Reports: Ethical Compliance, Security Analysis, Test Coverage, Formal Verification.

## <a name="core-api-endpoints"></a>Core API Endpoints

*(Focus on MVP - see [API Documentation](docs/api/api-endpoints.md) for future plans)*

| Endpoint                        | Method | Description                                                                       | Status (MVP)     |
| :---------------------------- | :----- | :------------------------------------------------------------------------------ | :--------------- |
| `/genesis/health`             | GET    | Check API server status. Returns `{"status": "ready"}`.                         | ✅ Working       |
| `/genesis/analyze-ethical`    | POST   | Analyzes Python code: Configurable Ethics, **Flake8 Quality**, Placeholder Tests. | ✅ MVP Core (Quality) |
| `/genesis/solve-math`         | POST   | Basic LLM integration test endpoint.                                            | ✅ Working (Test) |
| `/genesis/ethical/audit/{state_id}`   | GET    | Retrieve audit trail data (planned).                                            | ❌ Not Implemented |
| `/genesis/ethical/visualize/{state_id}` | GET    | Obtain visualization data (planned).                                      | ❌ Not Implemented |

**Sample MVP Request/Response - `/genesis/analyze-ethical`:**

[Example curl request and JSON response for `/genesis/analyze-ethical` - as in the original README]

## <a name="contributing"></a>Contributing

Contributions are welcome!  Please align with the current [Phase 2 Iteration 1 focus](ROADMAP.md) and see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines (basic guidelines currently, enhanced guidelines planned for Phase 2 Iteration 2).

## <a name="further-documentation"></a>Further Documentation

-   **[Full High-Level Specification (Detailed Vision)](SPECIFICATION.md)**
-   **[Development Roadmap (MVP & Beyond)](ROADMAP.md)**
-   **[Competitive Landscape Analysis](COMPETITIVE_LANDSCAPE.md)**
-   **[API Documentation (Placeholder - In Progress)](docs/api/api-endpoints.md)** - *Detailed API documentation for the `/genesis/analyze-ethical` endpoint will be available here by the end of Phase 2 Iteration 1 (Week 9).*
-   **[Contribution Guidelines](CONTRIBUTING.md)**
-   **[Full Markdown-Only Automation Workflow Guide](docs/workflows/markdown_automation.md)**  **(NEW - Recommended for streamlined AI-driven development)**

## <a name="troubleshooting"></a>Troubleshooting

### LLM API Key Errors
-   **Verify API Keys in `.env`:** Ensure API keys are correct in `.env`.
-   **Check `LLM_PROVIDER`:** Verify `LLM_PROVIDER` is set correctly in `.env` (`gemini` or `huggingface`).
-   **Key Validity:** Check API key validity in your provider's console.
-   **Typographical Errors:** Double-check for typos in `.env`.

### Docker Compose Issues (Redis/ZAP)
-   **Ensure Docker Desktop is Running:** Verify Docker Desktop is running.
-   **Check Container Status:** Use `docker ps` to check container status. Use `docker-compose logs redis` or `docker-compose logs zap` for errors.
-   **Port Conflicts:** Check for port conflicts (`docker ps -a`).
-   **`docker-compose.yml` Existence:** Ensure `docker-compose.yml` exists in the project root.
-   **Restart Docker:** Try restarting Docker Desktop.

### Python Dependency Errors
-   **Verify Python Version:**  `python --version` (must be 3.11+).
-   **Virtual Environment Activation:** Ensure `venv` is activated (`(venv)` in prompt).
-   **Upgrade pip:** `pip install --upgrade pip`.
-   **Re-install Dependencies:** `pip install -r requirements/base.txt` and `pip install -r requirements/dev.txt`.
-   **`flake8` Installation:** Verify `flake8` is installed (`pip install -r requirements/dev.txt`).
-   **Cache Issues:** `pip cache purge` and reinstall dependencies.

### API Connection Errors
-   **Flask Server Running:** Run `python src/api/server.py`.
-   **Host and Port:** Check server address (`http://127.0.0.1:5000`).
-   **Docker Container Ports:** Verify port mappings in `docker-compose.yml` (5000:5000).
-   **Firewall:** Check firewall rules blocking port 5000.

### Ethical Policy Errors
-   **Policy File Existence:** Ensure policy files (`.json`) are in `policies/`.
-   **File Paths:** Verify file paths in `src/api/routes/ethical_endpoints.py`.
-   **JSON Syntax:** Validate policy files for correct JSON.
-   **Schema Compliance:** Ensure policies match `ethical_policy_schema.json`.

### Code Quality Issues Not Reported
-   **`flake8` Installation:** Verify `flake8` is installed (`pip install -r requirements/dev.txt`).
-   **Server Logs:** Check Flask server logs for `CodeReviewAgent` or `flake8` errors.
-   **API Response Structure:** Verify `code_quality` section in API response JSON.
-   **Flake8 Executable Path:** Ensure `flake8` is in your system's PATH or venv's `bin`.

### Known Issues

#### ZAP Service (Local `docker-compose.yml`) Issue
-   **Local ZAP Unreliable in MVP:** Local ZAP service in `docker-compose.yml` may not be reliable for local security scans in this MVP release.
-   **CI Pipeline ZAP Scans Reliable:** Rely on ZAP Baseline Scan reports in CI pipeline runs for security vulnerability assessments.
-   **Local ZAP Scans Not Reliable for MVP:** Local ZAP scans via `docker-compose up` are not currently reliable.
-   **Resolution Planned Post-MVP:** Resolution for local ZAP service is planned for a future release.
-   **Note:** Code quality reporting via Flake8 is verified and functional for both local and CI pipeline use.

## <a name="license"></a>License

This project is licensed under the GNU Affero General Public License v3.0 (AGPLv3). See the `LICENSE` file for details. Aligned with OECD AI Principles and supports GDPR/Brexit compliance goals.

## <a name="contact"></a>Contact

tomwolfe@gmail.com

## <a name="disclaimer"></a>Disclaimer

**MVP Development Phase:** This project is in MVP development and not intended for production use. APIs and formats may change. Core functionality is integrated but undergoing final polish and internal testing.

---
