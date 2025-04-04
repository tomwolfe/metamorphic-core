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
    *   [Installation](#installation)
    *   [Running the API Server](#running_the_api_server)
    *   [Quickstart Guide](#quickstart_guide)
    *   [System Requirements](#system-requirements)
*   [Core API Endpoints](#core-api-endpoints)
*   [Contributing](#contributing)
*   [Detailed Documentation Links](#detailed-documentation-links)
*   [License](#license)
*   [Contact](#contact)
*   [Disclaimer](#disclaimer)
*   [Troubleshooting](#troubleshooting)
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
- Python 3.11+
- Docker & Docker Compose (Optional, for Redis/ZAP)
- Google Gemini API Key (Required)
- Hugging Face API Key (Optional)
- Git

### Installation <a name="installation"></a>
1.  **Clone:** `git clone https://github.com/tomwolfe/metamorphic-core.git && cd metamorphic-core`
2.  **Env Vars:** `cp .env.example .env` (Edit `.env` with your `GEMINI_API_KEY` minimum)
3.  **Services (Optional):** `docker-compose up -d redis zap`
4.  **Virtual Env:**
    ```bash
    python -m venv venv
    source venv/bin/activate # Linux/macOS
    # venv\Scripts\activate # Windows
    ```
5.  **Dependencies:**
    ```bash
    pip install --upgrade pip
    pip install -r requirements/base.txt
    pip install -r requirements/dev.txt # Required for Flake8 used by CodeReviewAgent
    ```

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
  -d '{"code": "def add(a, b):\n  \"\"\"Adds two numbers.\"\"\"\n  return a + b\n\nprint(add(1, 2))"}'
```
Check the response for `code_quality` results alongside `ethical_analysis`.
The `code_quality` section will now also be present in the response.
The `code_quality` section in the API response is now reliably populated with Flake8 analysis results, verified by integration tests.

### System Requirements <a name="system-requirements"></a>
- **Python**: 3.11+ is required for optimal performance and compatibility.
- **Docker**: Optional, but recommended for running Redis caching and OWASP ZAP security scanning services.
- **API Keys**:
  - **Gemini API Key (Required):** Essential for utilizing the default Gemini Language Model provider.
  - **Hugging Face API Key (Optional):** Required if you intend to use the Hugging Face Language Model provider.

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

See `CONTRIBUTING.md` (to be created) for detailed guidelines. Look for issues related to Phase 2 Iteration 1 tasks.

## Detailed Documentation Links <a name="detailed-documentation-links"></a>

*   [**Full High-Level Specification (Detailed Vision)**](SPECIFICATION.md)
*   [**Development Roadmap (MVP & Beyond)**](ROADMAP.md)
*   [**Competitive Landscape Analysis**](COMPETITIVE_LANDSCAPE.md)
*   *(Future Link: Detailed API Documentation)*
*   *(Future Link: Contribution Guidelines)*

## License <a name="license"></a>

This project is licensed under the GNU Affero General Public License v3.0 (AGPLv3). See the `LICENSE` file for details. Designed to adhere to OECD AI Principles and support GDPR/Brexit compliance goals.

## Contact <a name="contact"></a>

tomwolfe@gmail.com

## Disclaimer <a name="disclaimer"></a>

**MVP Development Phase:** Not for production. Core functionality is integrated but undergoing final polish and internal testing (Week 6). APIs/formats may have minor changes before internal release.

## Troubleshooting <a name="troubleshooting"></a>

**Common Issues & Solutions:**

*   **LLM API Key Errors:** Verify API keys in `.env` and the `LLM_PROVIDER` setting. Ensure keys are valid and active. Check for typos.
*   **Docker Compose Issues (Redis/ZAP):** Ensure Docker is running, check for port conflicts (`docker ps`), and examine logs (`docker-compose logs redis` or `docker-compose logs zap`). Make sure `docker-compose.yml` exists and is configured.
*   **Python Dependency Errors:** Ensure Python 3.11+ is used and the virtual environment (`venv`) is activated. Try `pip install --upgrade pip` then `pip install -r requirements/base.txt -r requirements/dev.txt`. Ensure `flake8` is installed (`dev.txt`).
*   **API Connection Errors:** Ensure the Flask server (`python src/api/server.py`) is running. Check the host/port (usually `http://127.0.0.1:5000`). If using Docker, ensure the container is running and ports are mapped correctly. Check firewall settings.
*   **Ethical Policy Errors:** Ensure policy files exist in the `policies/` directory and conform to `ethical_policy_schema.json`. Check file paths used in `src/api/routes/ethical_endpoints.py` (e.g., `load_default_policy`). Verify JSON syntax.
*   **Code Quality Issues Not Reported:** Ensure `flake8` is installed in your virtual environment (`pip install -r requirements/dev.txt`). Check server logs for errors related to `CodeReviewAgent` or `subprocess` calls to `flake8`. Verify the `code_quality` section exists in the API response.

**Known Issues:**
*   **ZAP Service (Local `docker-compose.yml`):** The ZAP service in `docker-compose.yml` may exit unexpectedly and is not reliably functional for local ZAP-based security scans in this MVP internal release.  **For MVP security vulnerability assessment, please rely on CI pipeline ZAP Baseline Scan reports.** Local ZAP scans are not reliable for MVP internal testing. Resolution of the local ZAP service issue is planned for a future release. **Important Note: Code quality analysis via Flake8 is verified and fully functional in the MVP for both local and CI pipeline use.**

## Terminology Footnotes <a name="terminology-footnotes"></a>

*(Terminology footnotes content - unchanged)*
