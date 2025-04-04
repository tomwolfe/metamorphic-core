# Metamorphic Software Genesis Ecosystem 🚀

[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/yourusername/metamorphic-core/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-AGPLv3-blue.svg)](LICENSE)
[![Roadmap Status](https://img.shields.io/badge/Roadmap-See_ROADMAP.md_for_Phase_2_and_Beyond-yellow)](ROADMAP.md)

**Version ∞: An Ever-Evolving Framework for Software Excellence** ✨

---

**🎯 CURRENT FOCUS: PHASE 2 ITERATION 1 - ENHANCEMENTS & FEATURE EXPANSION (Weeks 7-9)**

*   **Goal:** Begin Phase 2 Iteration 1 Development - Enhancements & Feature Expansion (Starting Week 7 - Late April 2025). See [**ROADMAP.md - Phase 2 Iteration 1**](ROADMAP.md#roadmap-phase-2---iteration-1-weeks-7-9) for detailed tasks.
*   **Key Objectives for Phase 2 Iteration 1:**
    *   **Enhanced Test Generation:** Re-integrate and expand MVP test generation logic (see [ROADMAP.md - Enhanced Test Generation](ROADMAP.md#roadmap-phase-2---iteration-1-weeks-7-9)).
    *   **Security Integration:** Integrate ZAP security scans into the `/genesis/analyze-ethical` API endpoint (see [ROADMAP.md - Security Integration](ROADMAP.md#roadmap-phase-2---iteration-1-weeks-7-9)).
    *   **API Documentation:** Detailed documentation for the `/genesis/analyze-ethical` API endpoint (see [ROADMAP.md - Documentation & Refactoring](ROADMAP.md#roadmap-phase-2---iteration-1-weeks-7-9)).
*   **Status:**
    *   Phase 1 MVP IS NOW COMPLETE ✅. Moving to Phase 2 Iteration 1 Development in Week 7.
    *   **See:** [**ROADMAP.md**](ROADMAP.md) for the detailed Phase 1 MVP plan (Week 6 Tasks) and future Phase 2 Iteration 1 planning.
    *   **NEXT PHASE FOCUS (Week 7+):** See [**ROADMAP.md - Phase 2 Iteration 1**](ROADMAP.md#roadmap-phase-2---iteration-1-weeks-7-9) for initial Phase 2 Iteration 1 planning. **Priorities for Phase 2 Iteration 1 are refined based on initial MVP internal testing feedback.**  Refer to the [**SPECIFICATION.md - Phase 2 Iteration 1 Focused Specification Summary**](SPECIFICATION.md#phase-2-iteration-1-focused-specification-summary) for a concise overview of the specification elements relevant to this iteration.

---

**Driven by AI and guided by a comprehensive specification, the Metamorphic Software Genesis Ecosystem is redefining software development through self-evolving, ethical, and secure solutions.**

This framework aims to autonomously generate, maintain, and evolve software from high-level requirements, integrating ethical governance, security analysis, automated testing, and formal verification capabilities.

**Table of Contents**
*   [Vision](#vision)
*   [Key Objectives](#key-objectives)
*   [Key Highlights of Current Capabilities](#key-highlights-of-current-capabilities)
*   [Showcase: Ideal Project Workflow Example](#showcase-ideal-project-workflow-example)
*   [Envisioned Conceptual Workflow](#envisioned-conceptual-workflow)
*   [Getting Started](#getting-started)
    *   [Prerequisites](#prerequisites)
        *   **Python Version:** Ensure you are using **Python 3.11+**. Check your version with `python --version`.
        *   **Docker:**  [Install Docker Desktop](https://www.docker.com/products/docker-desktop/) (optional, but recommended for Redis/ZAP).
        *   **API Keys:** Obtain the necessary API keys (see [API Keys](#api-keys) section below).
        *   **Git:** Ensure Git is installed on your system.
    *   [Installation](#installation)
        *   **Verify Python:** `python --version` (must be 3.11+)
        *   **Clone:** `git clone https://github.com/tomwolfe/metamorphic-core.git && cd metamorphic-core`
        *   **Env Vars:** `cp .env.example .env` (Edit `.env` with your API keys - see [`.env` Configuration](#env-configuration))
        *   **Services (Optional):** `docker-compose up -d redis zap` (ensure Docker is running first)
        *   **Virtual Env:**
            ```bash
            python -m venv venv
            source venv/bin/activate # Linux/macOS
            # venv\Scripts\activate # Windows
            ```
        *   **Dependencies:**
            ```bash
            pip install --upgrade pip
            pip install -r requirements/base.txt
            pip install -r requirements/dev.txt # Required for Flake8 used by CodeReviewAgent
            ```
        *   **Pre-commit Hooks (Optional but Recommended):** `pre-commit install` (requires `pre-commit` to be installed - see `requirements/dev.txt`)
    *   [Running the API Server](#running_the_api_server)
    *   [Quickstart Guide](#quickstart_guide)
    *   [System Requirements](#system-requirements)
        *   **Operating System:** Linux, macOS, Windows (tested on Ubuntu, macOS, Windows 10/11).
        *   **Python:** 3.11+ (required).
        *   **Docker:** Optional (but recommended for services). [Troubleshooting Docker Issues](#troubleshooting-docker-compose-issues).
        *   **RAM:** Minimum 8GB recommended, 16GB+ for optimal performance with LLM features.
        *   **Disk Space:** 2GB+ free disk space.
    *   [API Keys](#api-keys)
        *   **Gemini API Key (Required):** Get your key from [Google AI Studio](https://ai.google.dev/). Set `GEMINI_API_KEY` in `.env`.
        *   **Hugging Face API Key (Optional):**  Get your key from [Hugging Face](https://huggingface.co/settings/tokens). Set `HUGGING_FACE_API_KEY` in `.env` if using Hugging Face models.
        *   **GitHub API Key (Optional):** For future GitHub integrations. Set `YOUR_GITHUB_API_KEY` in `.env`.
        *   **ZAP API Key (Optional):** For local ZAP security scans (advanced). Set `ZAP_API_KEY` in `.env`.
    *   [`.env` Configuration](#env-configuration)
        *   Create a `.env` file by copying `.env.example`: `cp .env.example .env`
        *   **Required:** Set `GEMINI_API_KEY=your_gemini_api_key` with your actual Gemini API key.
        *   **Optional:** Configure other variables as needed (see `.env.example` for details).
        *   **Security Note:** **Never commit your `.env` file** to version control as it contains sensitive API keys. Ensure `.env` is in your `.gitignore`.
*   [Core API Endpoints](#core-api-endpoints)
*   [Contributing](#contributing)
    *   See [CONTRIBUTING.md](CONTRIBUTING.md) for contribution guidelines. (Contribution guidelines are currently basic, but will be expanded in Phase 2 Iteration 2).
*   [Detailed Documentation Links](#detailed-documentation-links)
    *   [**Full High-Level Specification (Detailed Vision)**](SPECIFICATION.md)
    *   [**Development Roadmap (MVP & Beyond)**](ROADMAP.md)
    *   [**Competitive Landscape Analysis**](COMPETITIVE_LANDSCAPE.md)
    *   [**API Documentation (Placeholder - In Progress)**](docs/api/api-endpoints.md) - *Detailed API documentation for the `/genesis/analyze-ethical` endpoint will be available here by the end of Phase 2 Iteration 1 (Week 9).*
    *   [**Contribution Guidelines**](CONTRIBUTING.md) - *Basic contribution guidelines are available. Enhanced guidelines and community contribution workflows are planned for Phase 2 Iteration 2.*
*   [License](#license)
*   [Contact](#contact)
*   [Disclaimer](#disclaimer)
*   [Troubleshooting](#troubleshooting)
    *   [LLM API Key Errors](#troubleshooting-llm-api-key-errors)
    *   [Docker Compose Issues (Redis/ZAP)](#troubleshooting-docker-compose-issues)
    *   [Python Dependency Errors](#troubleshooting-python-dependency-errors)
    *   [API Connection Errors](#troubleshooting-api-connection-errors)
    *   [Ethical Policy Errors](#troubleshooting-ethical-policy-errors)
    *   [Code Quality Issues Not Reported](#troubleshooting-code-quality-issues-not-reported)
    *   [Known Issues](#troubleshooting-known-issues)
        *   [ZAP Service (Local `docker-compose.yml`) Issue](#troubleshooting-zap-service-local-docker-composeyml-issue)
*   [Terminology Footnotes](#terminology-footnotes)

---

## Vision <a name="vision"></a>

To create an AI-driven framework that autonomously generates, maintains, and evolves **secure, ethical, and high-performance** software solutions **from high-level specifications**, continuously improving its own capabilities through feedback and self-refinement.

## Key Objectives <a name="key-objectives"></a>

-   **Autonomous Generation:** Generate functional software applications directly from natural language or structured specifications.
-   **Ethical Governance:** Integrate and enforce **configurable** ethical policies throughout the development lifecycle.
-   **Automated Quality & Security:** Implement continuous, automated testing (unit, integration, HIL), code review (style via **Flake8**, logic, security vulnerabilities), and **formal verification**.
-   **Self-Improving Development Process:** Continuously refine and optimize its own development processes using AI-driven planning and risk assessment.
-   **Self-Improvement:** Enable the framework to learn from analysis results, user feedback, and performance metrics to enhance its generation, analysis, and ethical enforcement capabilities.

*(For the full detailed vision and architecture, see [**SPECIFICATION.md**](SPECIFICATION.md))*

## Key Highlights of Current Capabilities <a name="key-highlights-of-current-capabilities"></a>

*(As of Week 6, focusing on MVP)*

-   **Code Analysis**: Static analysis with **Flake8** via API (`CodeReviewAgent`). **Integrated into `/genesis/analyze-ethical`. Flake8 code quality analysis: fully integrated and verified (through integration tests).**
-   **Security Scanning**: Automated DAST via OWASP ZAP integration is **actively running in the CI pipeline** using GitHub Actions, providing baseline security checks for each code change.  **Note:** For this MVP internal release, the ZAP service in `docker-compose.yml` has a known issue and may not function as expected locally.  Please rely on the CI pipeline for verified security scan results during this MVP phase. **However, code quality analysis via Flake8 is now verified and fully functional in the MVP.**
-   **Ethical Assessment**: **JSON-configurable** rule-based engine (`EthicalGovernanceEngine`) capable of dynamic enforcement based on loaded policies. **API integration tested and refined.**

**Note:** For MVP release, certain features (like Bandit SAST in `CodeReviewAgent`, advanced `TestGenAgent` logic) and some tests were intentionally *commented out* or *skipped* to prioritize core functionality and meet MVP release timelines. Phase 2 will focus on re-integrating these elements. See [**ROADMAP.md**](ROADMAP.md) for details.
**Note**: MVP completion requires final polish, internal testing, and addressing feedback (Week 6 tasks - see [ROADMAP.md](ROADMAP.md)).

## Showcase: Ideal Project Workflow Example <a name="showcase-ideal-project-workflow-example"></a>

To illustrate how MSGE is intended to work on an ambitious, high-value project, consider the generation of software for an **Autonomous Drone Package Delivery System**. This example leverages MSGE's core strengths in handling complexity, security, safety (as ethics), and hardware interaction.

**(This describes the final, improved version of the drone project workflow - Iteration 3)**

**1. Input:**
*   **High-Level Spec:** "Develop software for a drone delivery system: Cloud backend API + ESP32 firmware (connected to ArduPilot via MAVLink). ESP32 manages ultrasonics, camera (for QR code landing), EPMs (pickup/drop-off). Cloud manages missions & monitoring. Prioritize safety, security, reliability."
*   **Enhanced Requirements:** Explicit details added for standardized QR codes (size, material, error correction, quiet zone), onboard LED for QR scan illumination, downward ToF sensor for landing assist, robust QR detection logic (retries, confidence), graceful communication disconnect handling, redundant EPM commands, detailed state machine, comprehensive logging.
*   **Policy Files (JSON):**
    *   `safety_policy.json`: Geofences, altitudes, sensor checks, speed limits, EPM fail-safes, ToF usage rules, disconnect behaviors, conservative defaults.
    *   `privacy_policy.json`: Camera data handling (local QR processing), location anonymization.
    *   `security_policy.json`: Encrypted comms, secure auth, command integrity.

**2. Refinement (`SpecificationAnalysisAgent` & `LLMOrchestrator`):**
*   MSGE clarifies ambiguities via LLM interaction, focusing on the *enhanced* details (ToF model, LED control, QR parameters, disconnect state logic, etc.).
*   Refined specs, including hardware interfaces and detailed logic requirements, are stored semantically in the Knowledge Graph (KG).

**3. Design (AI Agents & KG):**
*   MSGE proposes the architecture (Cloud: Python/Go API, DB, Cache; ESP32: C++/MicroPython, drivers, RTOS tasks; Comms: MQTTs/HTTPS).
*   The design explicitly incorporates the ToF sensor, LED control, detailed state machine, and other enhancements into the ESP32 firmware plan within the KG.

**4. Generation (`CodeGenerationAgent` & `LLMOrchestrator`):**
*   MSGE generates code for the Cloud Backend API and the *enhanced* ESP32 firmware.
*   Firmware code includes drivers/logic for ToF sensor usage (landing assist), LED control (QR illumination), robust QR detection/search algorithms, the specified state machine for disconnect handling, redundant EPM commands, and comprehensive logging, all drawing context from the KG.

**5. Validation (Iterative Loop with Human Oversight Potential):**
*   Generated code undergoes rigorous checks against the *enhanced* requirements. This is a cyclical feedback loop.
*   **Checks:** `CodeReviewAgent` (**Flake8 quality**), `EthicalGovernanceEngine` (safety/privacy policies), `SecurityAgent` (DAST, SAST, dependencies, security policy), `TestGenerationAgent` (unit, integration, **Hardware-in-the-Loop (HIL)** simulation tests), `FormalVerificationEngine` (proofs for critical logic like EPM safety).
*   **Feedback & Regeneration:** Validation results are fed back. If failures occur, the `LLMOrchestrator` directs `CodeGenerationAgent` to fix the specific issues. The LLM uses the direct feedback *and may query the KG for context on similar past fixes or relevant design patterns* to generate corrected code. The corrected code then re-enters the validation step. **This loop repeats until the generated code passes all configured checks.**
*   **Human Oversight Point (Optional):** For critical failures (e.g., complex security vulnerability, failed safety proof, persistent ethical violation), the system could flag the issue for human review before attempting further automated regeneration.

**6. Integration:**
*   Once validation passes (potentially including human sign-off), validated cloud code is deployed; enhanced ESP32 firmware compiled into a flashable binary. CI/CD runs final checks.

**7. Improvement (`ContinuousLearningCore` & KG):**
*   MSGE analyzes operational data (mission logs, ToF readings, QR success rates, disconnect events) stored in the KG.
*   It identifies patterns (e.g., QR failures in specific conditions) and can suggest or implement refined parameters (camera settings, timeouts) or algorithmic changes in future generation cycles.

**End Product of this MSGE Workflow:**

*   **Software Artifacts:** Ready-to-deploy Cloud Backend code, ready-to-flash enhanced ESP32 Firmware binary, comprehensive test suites (including HIL), configuration/policy files, formal verification artifacts.
*   **MSGE Reports (Evidence):** Ethical Compliance Report (vs updated policies), Security Analysis Report, Test Coverage & HIL Report (validating enhanced features), Formal Verification Certificate.

## Envisioned Conceptual Workflow <a name="envisioned-conceptual-workflow"></a>

1.  **Input**: High-level software description + detailed policies/constraints.
2.  **Refinement**: AI clarifies requirements (`SpecificationAnalysisAgent`).
3.  **Design**: AI generates software architecture (stored in KG).
4.  **Generation**: `CodeGenerationAgent` produces code (Python, Go, Rust, JS/TS, C++) using LLMs managed by `LLMOrchestrator`.
5.  **Validation (Iterative Loop)**: Code Quality (`CodeReviewAgent` - **Flake8**), Ethical Assessment (`EthicalGovernanceEngine`), Security Scans (`SecurityAgent`), Testing (`TestGenAgent` - Unit, Integration, HIL), Formal Verification (`FormalVerificationEngine`). Feedback drives regeneration.
6.  **Integration**: Validated code integrated via Git; CI/CD pipeline runs checks.
7.  **Improvement**: `ContinuousLearningCore` analyzes performance/feedback to adapt agents/processes.

## Getting Started <a name="getting-started"></a>

### Prerequisites <a name="prerequisites"></a>
-   **Python Version:** Ensure you are using **Python 3.11+**. Check your version with `python --version`.
-   **Docker:**  [Install Docker Desktop](https://www.docker.com/products/docker-desktop/) (optional, but recommended for Redis/ZAP). [Troubleshooting Docker Installation](#troubleshooting-docker-installation).
-   **API Keys:** Obtain the necessary API keys (see [API Keys](#api-keys) section below).
-   **Git:** Ensure Git is installed on your system.

### Installation <a name="installation"></a>
1.  **Verify Python Version:**
    *   Open your terminal or command prompt.
    *   Run `python --version`.
    *   **Ensure the output is Python 3.11 or higher.** If not, [install Python 3.11+](https://www.python.org/downloads/).
2.  **Clone the Repository:**
    *   Open your terminal and navigate to the directory where you want to clone the project.
    *   Run: `git clone https://github.com/tomwolfe/metamorphic-core.git && cd metamorphic-core`
3.  **Configure Environment Variables:**
    *   Copy the example environment variables file: `cp .env.example .env`
    *   **Edit the `.env` file** to set your API keys and other configurations. See [`.env` Configuration](#env-configuration) for details.
4.  **Start Optional Services (Redis & ZAP with Docker Compose):**
    *   **Ensure Docker Desktop is running.** [Troubleshooting Docker Compose Issues](#troubleshooting-docker-compose-issues).
    *   Run: `docker-compose up -d redis zap`
5.  **Create and Activate a Virtual Environment (Recommended):**
    *   In your project directory, run: `python -m venv venv`
    *   Activate the virtual environment:
        *   **Linux/macOS:** `source venv/bin/activate`
        *   **Windows:** `venv\Scripts\activate`
    *   **(Important): Ensure your terminal prompt now shows `(venv-dev)` indicating the virtual environment is active.**
6.  **Install Python Dependencies:**
    *   **Upgrade pip (recommended):** `pip install --upgrade pip`
    *   Install base requirements: `pip install -r requirements/base.txt`
    *   Install development requirements (including Flake8): `pip install -r requirements/dev.txt`
7.  **Install Pre-commit Hooks (Optional but Highly Recommended):**
    *   **Ensure `pre-commit` is installed** (it's included in `requirements/dev.txt`).
    *   Run: `pre-commit install`
    *   Pre-commit hooks will now run automatically before each commit, helping to maintain code quality.

### Running the API Server <a name="running_the_api_server"></a>
```bash
# Ensure .env is configured & venv is active
python src/api/server.py
```
Server runs at `http://127.0.0.1:5000/`. Check health at `/genesis/health`.

### Quickstart Guide <a name="quickstart_guide"></a>
To quickly test the core MVP endpoint, follow these steps after installation and server startup:
```bash
curl -X POST \
  http://127.0.0.1:5000/genesis/analyze-ethical \
  -H "Content-Type": "application/json" \
  -d '{"code": "def calculate_area(radius):\n    \"\"\"Calculates the area of a circle.\"\"\"\n    if radius < 0:\n        raise ValueError(\"Radius cannot be negative\")\n    return 3.14159 * radius * radius"}'
```
Check the response for `code_quality` results alongside `ethical_analysis`.
The `code_quality` section will now also be present in the response.
The `code_quality` section in the API response is now reliably populated with Flake8 analysis results, verified by integration tests.

### System Requirements <a name="system-requirements"></a>
- **Operating System:** Linux (Ubuntu recommended), macOS, Windows (Windows 10/11 tested).
- **Python Version:** **Python 3.11+ is strictly required.**
- **Docker:** Optional, but highly recommended for running Redis caching and OWASP ZAP security scanning services. [Troubleshooting Docker Installation](#troubleshooting-docker-installation). [Troubleshooting Docker Compose Issues](#troubleshooting-docker-compose-issues).
- **RAM:** Minimum 8GB RAM recommended, 16GB+ for optimal performance, especially when using LLM-powered features.
- **Disk Space:** 2GB of free disk space or more.

### API Keys <a name="api-keys"></a>
- **Gemini API Key (Required):**
  - **How to Obtain:** Go to [Google AI Studio](https://ai.google.dev/) and create a project to get your API key.
  - **Configuration:** Set `GEMINI_API_KEY=your_gemini_api_key` in the `.env` file. **This key is essential for the core functionality of the Metamorphic Core MVP.**
- **Hugging Face API Key (Optional):**
  - **How to Obtain:** Sign up or log in at [Hugging Face](https://huggingface.co/) and create a new API token in your [settings/tokens](https://huggingface.co/settings/tokens) section.
  - **Configuration:** Set `HUGGING_FACE_API_KEY=your_huggingface_api_key` in `.env` **only if you plan to use Hugging Face Language Models.**
- **GitHub API Key (Optional):**
  - **How to Obtain:** Generate a personal access token with `repo` scope on [GitHub](https://github.com/settings/tokens).
  - **Configuration:** Set `YOUR_GITHUB_API_KEY=your_github_api_key` in `.env` **for future GitHub integrations (not required for MVP).**
- **ZAP API Key (Optional):**
  - **How to Obtain:** The ZAP service in `docker-compose.yml` uses a default API key (`changeme`). For enhanced security in production, you should configure a strong API key.
  - **Configuration:** Set `ZAP_API_KEY=your_zap_api_key` in `.env` **if you intend to use local ZAP security scans (advanced/optional for MVP).**

### `.env` Configuration <a name="env-configuration"></a>
-   **Create `.env` file:** Start by copying the `.env.example` file to `.env`: `cp .env.example .env`
-   **Set Required Gemini API Key:**
    -   Open the `.env` file in a text editor.
    -   Locate the line `GEMINI_API_KEY=your_key_here`
    -   **Replace `your_key_here` with your actual Gemini API key** obtained from [Google AI Studio](https://ai.google.dev/). Example: `GEMINI_API_KEY=AIzaSyABC123...XYZ789`
    -   **This is the only API key strictly required for basic MVP functionality.**
-   **Configure Optional API Keys and Settings:**
    -   Review the other variables in `.env.example` (e.g., `HUGGING_FACE_API_KEY`, `LLM_PROVIDER`, `LLM_TIMEOUT`, etc.) and **uncomment and configure them in your `.env` file only if needed.**
    -   Leave optional variables commented out if you are using the default settings.
-   **Security Best Practices:**
    -   **Important:** **Never commit your `.env` file to version control**, as it contains sensitive API keys.
    -   Ensure `.env` is listed in your project's `.gitignore` file to prevent accidental commits.
    -   Consider using environment variable management tools for more secure handling of secrets in production deployments.

## Core API Endpoints <a name="core-api-endpoints"></a>

*(Focus on MVP - see `docs/api/api-endpoints.md` for future plans)*

| Endpoint                        | Method | Description                                                                       | Status (MVP)     |
| :---------------------------- | :----- | :------------------------------------------------------------------------------ | :--------------- |
| `/genesis/health`             | GET    | Check API server status. Returns `{"status": "ready"}`.                         | ✅ Working       |
| `/genesis/analyze-ethical`    | POST   | Analyzes Python code: Configurable Ethics, **Flake8 Quality**, Placeholder Tests. | ✅ MVP Core (Quality) |
| `/genesis/solve-math`         | POST   | Basic LLM integration test endpoint.                                            | ✅ Working (Test) |
| `/genesis/ethical/audit/{state_id}`   | GET    | Retrieve audit trail data (planned).                                            | ❌ Not Implemented |
| `/genesis/ethical/visualize/{state_id}` | GET    | Obtain visualization data (planned).                                      | ❌ Not Implemented |

**Sample MVP Request/Response - `/genesis/analyze-ethical`**

**Request (Example using curl for code with potential Flake8 issues):**

```bash
curl --request POST \
  --url http://127.0.0.1:5000/genesis/analyze-ethical \
  --header 'Content-Type: application/json' \
  --data '{"code": "import os # F401\ndef add(a, b):\n  \"\"\"Adds two numbers.\"\"\"\n  # TODO: Add type hints\n  return a + b\n\nprint(add(1, 2))"}'
```

**Response (Example - *Reflecting Polished MVP State with Flake8 and Ethical Analysis*):**
```json
{
  "status": "approved", // Status determined dynamically by policy enforcement (assuming code is ethically compliant)
  "requested_policy_name": "Strict Bias Risk Policy", // Example policy name used (default)
  "code_quality": { // Populated by CodeReviewAgent (Flake8)
    "output": "/path/to/tempfile.py:1:1: F401 'os' imported but unused", // Example Flake8 finding - verified in integration tests
    "issues_found": 1 // Count of Flake8 issues
  },
  "ethical_analysis": { // Populated by EthicalGovernanceEngine (Dynamic)
    "policy_name": "Strict Bias Risk Policy", // Actual policy name used
    "description": "Zero tolerance for biased language",
    "overall_status": "approved", // Overall status from engine based on policy rules
    "BiasRisk": { // Example ethical constraint statuses - verified in integration tests
      "status": "compliant",
      "threshold": 0.1,
      "enforcement_level": 3,
      "details": "No violating keywords found."
    },
    "TransparencyScore": {
      "status": "compliant", // Docstring present
      "threshold": 0.5,
      "enforcement_level": 2,
      "details": "Docstring presence check passed (module/functions/classes)."
    },
    "SafetyBoundary": {
      "status": "compliant", // No obviously unsafe operations
      "threshold": 0.8,
      "enforcement_level": 2,
      "details": "No configured unsafe operations found."
    }
  },
  "generated_tests_placeholder": "import pytest\n# Placeholder tests - Integrate TestGenAgent" // Placeholder content - unchanged
}
```

## Contributing <a name="contributing"></a>

We welcome contributions! Please align with the current **Phase 2 Iteration 1 focus** outlined in [**ROADMAP.md**](ROADMAP.md) (primarily Week 7-9 tasks: **Re-integrating MVP test code**, Enhanced Test Generation, Security Agent API Integration, and API Documentation).

See [CONTRIBUTING.md](CONTRIBUTING.md) for detailed guidelines. (Contribution guidelines are currently basic, but will be expanded in Phase 2 Iteration 2). Look for issues related to Phase 2 Iteration 1 tasks.

## Detailed Documentation Links <a name="detailed-documentation-links"></a>

*   [**Full High-Level Specification (Detailed Vision)**](SPECIFICATION.md)
*   [**Development Roadmap (MVP & Beyond)**](ROADMAP.md)
*   [**Competitive Landscape Analysis**](COMPETITIVE_LANDSCAPE.md)
*   [**API Documentation (Placeholder - In Progress)**](docs/api/api-endpoints.md) - *Detailed API documentation for the `/genesis/analyze-ethical` endpoint will be available here by the end of Phase 2 Iteration 1 (Week 9).*
*   [**Contribution Guidelines**](CONTRIBUTING.md) - *Basic contribution guidelines are available. Enhanced guidelines and community contribution workflows are planned for Phase 2 Iteration 2.*

## License <a name="license"></a>

This project is licensed under the GNU Affero General Public License v3.0 (AGPLv3). See the `LICENSE` file for details. Designed to adhere to OECD AI Principles and support GDPR/Brexit compliance goals.

## Contact <a name="contact"></a>

tomwolfe@gmail.com

## Disclaimer <a name="disclaimer"></a>

**MVP Development Phase:** Not for production. Core functionality is integrated but undergoing final polish and internal testing (Week 6). APIs/formats may have minor changes before internal release.

## Troubleshooting <a name="troubleshooting"></a>

### LLM API Key Errors <a name="troubleshooting-llm-api-key-errors"></a>
-   **Verify API Keys in `.env`:** Double-check that your API keys are correctly entered in the `.env` file.
-   **Check `LLM_PROVIDER`:** Ensure the `LLM_PROVIDER` environment variable is set to the correct provider (`gemini` or `huggingface`) in `.env`.
-   **Key Validity:** Ensure your API keys are valid and active in your provider's developer console (Google AI Studio, Hugging Face).
-   **Typographical Errors:** Carefully check for typos in the variable names and API key values in `.env`.

### Docker Compose Issues (Redis/ZAP) <a name="troubleshooting-docker-compose-issues"></a>
-   **Ensure Docker Desktop is Running:** Verify that Docker Desktop application is running on your system.
-   **Check Container Status:** Use `docker ps` in your terminal to see if the `redis` and `zap` containers are running. If not, check container logs using `docker-compose logs redis` or `docker-compose logs zap` for errors.
-   **Port Conflicts:** Check for port conflicts using `docker ps -a`. If ports 6379 or 8080 are already in use, either stop the conflicting process or change the port mappings in `docker-compose.yml`.
-   **`docker-compose.yml` Existence:** Ensure that the `docker-compose.yml` file exists in the root of your project directory.
-   **Restart Docker:** Try restarting Docker Desktop if issues persist.

### Python Dependency Errors <a name="troubleshooting-python-dependency-errors"></a>
-   **Verify Python Version:** Run `python --version` to ensure you are using **Python 3.11 or higher**.
-   **Virtual Environment Activation:** Ensure your virtual environment (`venv`) is activated. Check if `(venv)` is shown at the beginning of your terminal prompt.
-   **Upgrade pip:** Run `pip install --upgrade pip` to ensure you have the latest pip version.
-   **Re-install Dependencies:** Try re-installing dependencies:
    ```bash
    pip install -r requirements/base.txt
    pip install -r requirements/dev.txt
    ```
-   **`flake8` Installation:** Ensure `flake8` is installed, as it is required for code quality checks: `pip install -r requirements/dev.txt`.
-   **Cache Issues:** Try clearing pip cache: `pip cache purge` and then re-installing dependencies.

### API Connection Errors <a name="troubleshooting-api-connection-errors"></a>
-   **Flask Server Running:** Ensure the Flask API server is running by executing `python src/api/server.py` in your terminal.
-   **Host and Port:** Check the server address (usually `http://127.0.0.1:5000`).
-   **Docker Container Ports:** If using Docker, ensure the container is running and ports are correctly mapped in `docker-compose.yml` (host port 5000 mapped to container port 5000).
-   **Firewall:** Check for firewall rules that might be blocking connections to port 5000.

### Ethical Policy Errors <a name="troubleshooting-ethical-policy-errors"></a>
-   **Policy File Existence:** Ensure policy files (`.json`) exist in the `policies/` directory.
-   **File Paths:** Verify the file paths used in `src/api/routes/ethical_endpoints.py` (e.g., `load_default_policy`) are correct.
-   **JSON Syntax:** Check policy files for valid JSON syntax. Use a JSON validator if needed.
-   **Schema Compliance:** Ensure policy files conform to the `ethical_policy_schema.json` schema.

### Code Quality Issues Not Reported <a name="troubleshooting-code-quality-issues-not-reported"></a>
-   **`flake8` Installation:** Double-check that `flake8` is installed in your virtual environment (`pip install -r requirements/dev.txt`).
-   **Server Logs:** Check the Flask server logs for any errors related to `CodeReviewAgent` or `subprocess` calls to `flake8`.
-   **API Response Structure:** Verify that the `code_quality` section exists in the API response JSON.
-   **Flake8 Executable Path:** In rare cases, ensure that the `flake8` executable is in your system's PATH or virtual environment's bin directory.

### Known Issues <a name="troubleshooting-known-issues"></a>

#### ZAP Service (Local `docker-compose.yml`) Issue <a name="troubleshooting-zap-service-local-docker-composeyml-issue"></a>
-   **Local ZAP Unreliable in MVP:** The ZAP service in `docker-compose.yml` may exit unexpectedly and is **not reliably functional for local ZAP-based security scans in this MVP internal release.**
-   **CI Pipeline ZAP Scans Reliable:** **For security vulnerability assessment, please rely on the automated ZAP Baseline Scan reports available in the CI pipeline runs for each Pull Request and Push to the `main` branch.**
-   **Local ZAP Scans Not Reliable for MVP:** Local ZAP scans using `docker-compose up` are not currently reliable for MVP internal testing.
-   **Resolution Planned Post-MVP:** Resolution of the local ZAP service issue is planned for a future release (post-MVP).
-   **Important Note: Code quality reporting via Flake8 is verified and functional in the MVP for both local and CI pipeline use.**

## Terminology Footnotes <a name="terminology-footnotes"></a>

*(Terminology footnotes content - unchanged)*

---
