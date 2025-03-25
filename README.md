# Metamorphic Software Genesis Ecosystem 🚀

[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-AGPLv3-blue.svg)](LICENSE)
[![Roadmap Status](https://img.shields.io/badge/Roadmap_Status-Phase_1_MVP_In_Progress-yellow)](https://github.com/tomwolfe/metamorphic-core/milestones?direction=asc&sort=due_date&state=open)

**Version ∞: An Ever-Evolving Framework for Software Excellence** ✨

**Driven by AI and guided by a comprehensive high-level specification and roadmap, the Metamorphic Software Genesis Ecosystem is redefining software development through self-evolving, ethical, and secure solutions.**

---

**Table of Contents**
* [Vision](#vision)
* [Key Objectives](#key-objectives)
* [Envisioned Workflow: From Concept to Code](#envisioned-workflow-from-concept-to-code)
* [Current Status](#current-status)
* [Key Highlights of Current Capabilities](#key-highlights-of-current-capabilities)
* [Roadmap Update - Phase 1 MVP](#roadmap-update---phase-1-mvp)
    * [Phase 1 MVP Definition](#phase-1-mvp-definition)
    * [Phase 1 Deliverables](#phase-1-deliverables)
    * [Phase 1 Actionable Steps (Version 1.3 - Revised 3 - *Final Revision*)](#phase-1-actionable-steps-version-13---revised-3---final-revision)
        * [Month 1: Refine Agents & Ethical Engine Foundation](#month-1-refine-agents--ethical-engine-foundation)
            * [Week 1: MVP API Endpoint Shell & Basic Agent Wiring](#week-1-mvp-api-endpoint-shell--basic-agent-wiring---get-the-api-talking-to-agents)
            * [Week 2: `CodeReviewAgent` MVP Functionality](#week-2--codereviewagent-mvp-functionality---flake8-focus)
            * [Week 3: `EthicalPolicyEngine` MVP Foundation](#week-3-ethicalpolicyengine-mvp-foundation---json-policy-loading--basic-enforcement)
            * [Week 4: `TestGenAgent` MVP & API Integration](#week-4-testgenagent-mvp--api-integration---placeholder-tests)
        * [Month 2: Integrate Agents & API Endpoint](#month-2-integrate-agents--api-endpoint)
            * [Week 5: Basic Constraint Enforcement Logic](#week-5--ethicalpolicyengine---basic-constraint-enforcement-logic-implementation-biasrisk-transparencyscore-safety-boundary)
            * [Week 6: API Polish & Error Handling](#week-6--api-endpoint-response-refinement--basic-error-handling---polish-api-output)
            * [Week 7: README Documentation](#week-7--documentation---mvp-api-usage-guide)
            * [Week 8: Internal Release & Testing](#week-8--mvp-internalalpha-release--initial-testing---first-release--feedback)
        * [Month 3: MVP Refinement & Documentation](#month-3-mvp-refinement--documentation)
    * [Phase 1 MVP - Internal Metrics Tracking](#phase-1-mvp---internal-metrics-tracking)
    * [Gantt Chart: Phase 1 MVP Roadmap](#gantt-chart-phase-1-mvp-roadmap)
    * [Roadmap Optimization Tricks (Refined for MVP Focus)](#roadmap-optimization-tricks-refined-for-mvp-focus)
    * [Beyond Month 2 (Future Iterations)](#beyond-month-2-future-iterations)
* [Getting Started](#getting-started)
    * [Prerequisites](#prerequisites)
    * [Installation](#installation)
    * [Running the API Server](#running_the_api_server)
    * [Quickstart Guide](#quickstart_guide)
    * [System Requirements](#system-requirements)
* [API Endpoints](#api-endpoints)
    * [Sample MVP Request/Response - `/genesis/analyze-ethical`](#sample-mvp-requestresponse---genesisanalyze-ethical)
    * [Core API Endpoints](#core-api-endpoints)
* [Contributing](#contributing)
* [License](#license)
* [License and Compliance](#license-and-compliance)
* [Contact](#contact)
* [Disclaimer](#disclaimer)
* [Troubleshooting](#troubleshooting)
* [Terminology Footnotes](#terminology-footnotes)

---

## Vision <a name="vision"></a>

To create a self-refining, AI-driven framework capable of independently generating, maintaining, and evolving high-quality software solutions, operating as a perpetual engine of innovation and improvement.

## Key Objectives <a name="key-objectives"></a>

- **Autonomous Software Development**: Enable independent creation of complete software applications.
- **Ethical Assurance**: Integrate robust ethical governance. *MVP: JSON policy loading/validation and basic rule-based enforcement.*
- **Continuous Quality**: Automate testing, code review, and security analysis.
- **Self-Enhancement**: Enable the ecosystem to learn, adapt, and improve.

## Envisioned Workflow: From Concept to Code <a name="envisioned-workflow-from-concept-to-code"></a>

1.  **User Input**: High-level software description.
2.  **Specification Refinement**: AI clarifies input.
3.  **Design & Planning**: Generate architecture.
4.  **Code Generation**: Produce code.
5.  **Testing & Validation**:
    *   Unit, integration, E2E tests.
    *   Code quality (Flake8).
    *   Ethical assessment (JSON policy loading, basic rule engine, quantum-inspired analysis<sup>1</sup>).
    *   Security scans (OWASP ZAP, Bandit).
6.  **Continuous Integration**: GitHub Actions CI/CD.
7.  **Self-Improvement**: Learn and adapt.

## Current Status <a name="current-status"></a>

The ecosystem is an **AI-powered code analysis, ethical validation, and security scanning framework** under active development. Fully autonomous software generation is the long-term goal.

**Phase 1 Capabilities - Week 3 Month 1 Achieved** ✅

**Note:** Phase 1 MVP focuses on foundational capabilities. Advanced logic for ethical assessment and test generation will follow post-MVP.

### Key Milestones Achieved (Month 1):
- **Week 1:** ✅ API Endpoint Shell, Basic Agent Wiring, API Response Structure, Minimal Integration Tests.
- **Week 2:** ✅ `CodeReviewAgent` MVP (Flake8 Integration & Testing), API Integration (`code_quality`), Expanded Integration Tests.
- **Week 3:** ✅ `EthicalPolicyEngine` MVP Foundation:
    *   **[✅] JSON Support:** Schema defined, examples created, loading & validation implemented.
    *   **[✅] Basic Enforcement:** Rule-based checks for Bias (keywords), Transparency (docstrings), Safety (unsafe ops).
    *   **[✅] Testing:** Unit tests for loading/enforcement, integration tests for API `ethical_analysis` section.

### Technical Foundations Live:
- **LLM Orchestration:** Gemini/Hugging Face layer operational.
- **Security Scanning:** OWASP ZAP baseline scans functional.
- **Knowledge Graph:** Operational KG for system knowledge.
- **Ethical Validation:** Foundational framework (JSON policy loading, basic rule engine, quantum-inspired analysis).
- **Code Analysis:** `CodeReviewAgent` (Flake8), `TestGenAgent` (placeholder generation).
- **Context Management:** Initial mechanisms for long contexts.
- **CI/CD:** Automated GitHub Actions workflow (✅ Passing).
- **Formal Verification:** Initial Coq integration.

## Key Highlights of Current Capabilities <a name="key-highlights-of-current-capabilities"></a>

- **Code Analysis**: Static analysis with Flake8 via API.
- **Security Scanning**: Automated OWASP ZAP integration.
- **Ethical Assessment Foundation**: JSON policy loading/validation functional. Basic rule-based enforcement (Bias, Transparency, Safety) implemented for MVP.
- **LLM Powered Features**: Utilizes Gemini and Hugging Face models.
- **CI/CD Pipeline**: Fully automated GitHub Actions pipeline.
- **Knowledge Graph Backbone**: Centralized KG operational.

**Note**: Functions as an AI-powered code quality/analysis and basic ethical assessment tool. MVP enforcement uses simple rules despite JSON loading capability. Full autonomy, Bandit integration, and advanced ethical logic are future goals.

## Roadmap Update - Phase 1 MVP <a name="roadmap-update---phase-1-mvp"></a> 🚧

**Roadmap for Completion (Iterative MVP Approach)**

#### Phase 1 MVP Definition <a name="phase-1-mvp-definition"></a>

Functional `/genesis/analyze-ethical` API providing:
1.  **Basic Ethical Analysis:** Rule-based checks using loaded JSON policies (Bias keyword, Docstring presence, Unsafe op string).
2.  **Basic Code Quality:** Flake8 reporting via `CodeReviewAgent`.
3.  **Placeholder Tests:** Basic pytest placeholder code generation via `TestGenAgent` (string response, not executed).
4.  **API Access:** Functional endpoint integrating the above.

#### Phase 1 Deliverables <a name="phase-1-deliverables"></a>

1. Functional `/genesis/analyze-ethical` API endpoint.
2. Basic Ethical Policy Engine (JSON loading functional, basic rule enforcement).

#### Phase 1 Actionable Steps (Version 1.3 - Revised 3 - *Final Revision*) <a name="phase-1-actionable-steps-version-13---revised-3---final-revision"></a>

##### Month 1: Refine Agents & Ethical Engine Foundation <a name="month-1-refine-agents--ethical-engine-foundation"></a> ✅ COMPLETE
* **Weekly Breakdown:**
    * ##### Week 1: MVP API Endpoint Shell & Basic Agent Wiring <a name="week-1-mvp-api-endpoint-shell--basic-agent-wiring---get-the-api-talking-to-agents"></a> ✅ COMPLETE
    * ##### Week 2: `CodeReviewAgent` MVP Functionality <a name="week-2--codereviewagent-mvp-functionality---flake8-focus"></a> ✅ COMPLETE
    * ##### Week 3: `EthicalPolicyEngine` MVP Foundation <a name="week-3-ethicalpolicyengine-mvp-foundation---json-policy-loading--basic-enforcement"></a> ✅ COMPLETE
    * ##### Week 4: `TestGenAgent` MVP & API Integration <a name="week-4-testgenagent-mvp--api-integration---placeholder-tests"></a> 🚧 In Progress
        *   **Task 4.1:** Implement MVP Placeholder Test Generation.
        *   **Task 4.2:** Add Unit Tests (Placeholder Generation).
        *   **Task 4.3:** Integrate `TestGenAgent` into API Endpoint.
        *   **Integration Testing:** Expand for `generated_tests_placeholder`.

##### Month 2: Integrate Agents & API Endpoint <a name="month-2-integrate-agents--api-endpoint"></a>
* **Weekly Breakdown:**
    * ##### Week 5: Basic Constraint Enforcement Logic <a name="week-5--ethicalpolicyengine---basic-constraint-enforcement-logic-implementation-biasrisk-transparencyscore-safety-boundary"></a> ✅
    * ##### Week 6: API Polish & Error Handling <a name="week-6--api-endpoint-response-refinement--basic-error-handling---polish-api-output"></a>
    * ##### Week 7: README Documentation <a name="week-7--documentation---mvp-api-usage-guide"></a>
    * ##### Week 8: Internal Release & Testing <a name="week-8--mvp-internalalpha-release--initial-testing---first-release--feedback"></a>

##### Month 3: MVP Refinement & Documentation <a name="month-3-mvp-refinement--documentation"></a>

#### Phase 1 MVP - Internal Metrics Tracking <a name="phase-1-mvp---internal-metrics-tracking"></a>
*(Percentages reflect progress towards achieving *MVP* feature scope)*

**Contribution Sprint Queue (Phase 1 MVP - Next Tasks):**

Focus is on completing **Month 1, Week 4:**

1.  **`TestGenAgent` - Placeholder Generation:** Implement basic pytest placeholder generation. ([See Task 4.1](#week-4-testgenagent-mvp--api-integration---placeholder-tests))
2.  **`TestGenAgent` - Unit Testing:** Add unit tests for placeholder generation. ([See Task 4.2](#week-4-testgenagent-mvp--api-integration---placeholder-tests))
3.  **API Integration - `TestGenAgent`:** Integrate into API, return placeholder code string. ([See Task 4.3](#week-4-testgenagent-mvp--api-integration---placeholder-tests))
4.  **Expand Integration Tests:** Verify `generated_tests_placeholder` field. ([See Task 4.3](#week-4-testgenagent-mvp--api-integration---placeholder-tests))

<details>
<summary>Click to expand Phase 1 MVP Internal Metrics Tracking Table</summary>

| Roadmap Item                                  | Effort Completed (Dev %) | Functionality Validated (MVP %) | Status                | Next Steps                                                                          |
| :-------------------------------------------- | :-----------------------: | :-----------------------------: | :-------------------- | :---------------------------------------------------------------------------------- |
| MVP Deliverable 1: API Endpoint              |            95%            |               90%               | Implemented           | Integrate `TestGenAgent` (Wk4). Polish error handling & response (Wk6).             |
| MVP Deliverable 2: Configurable Policy Engine |            90%            |               80%               | Implemented (MVP)     | MVP scope complete.                                                                 |
| TestGenAgent Refinement                       |            30%            |               10%               | In Progress           | Complete Week 4 tasks (placeholder generation, tests, API integration).             |
| CodeReviewAgent Refinement                      |           100%            |              100%               | Implemented (MVP)     | MVP scope complete.                                                                 |
| JSON Schema Design                             |           100%            |              100%               | Implemented (MVP)     | MVP scope complete.                                                                 |
| Ethical Policy Engine (JSON Configurable)      |            90%            |               80%               | Implemented (MVP)     | MVP scope complete.                                                                 |
| GDPR/COPPA Placeholder API                     |            70%            |               60%               | Partially Implemented | Documentation deferred post-MVP.                                                    |
| Bias Detection Module Integration             |            20%            |               10%               | Planned               | Deferred post-MVP.                                                                  |
| **API Endpoint Integration Task**              |            85%            |               80%               | Partially Implemented | Integrate `TestGenAgent` (Wk4). Implement response/error refinements (Wk6). Tests. |

</details>

#### Gantt Chart: Phase 1 MVP Roadmap <a name="gantt-chart-phase-1-mvp-roadmap"></a>
```mermaid
gantt
    title Metamorphic Software Genesis Ecosystem Roadmap
    dateFormat  YYYY-MM-DD
    axisFormat %Y-%m-%d

    section Phase 1: MVP
    Month 1: Core Agent Refinement :crit, done, 2025-03-22, 30d
    Month 2: API Integration & Polish :active, 2025-04-22, 30d
    Month 3: MVP Release & Feedback : 2025-05-22, 30d

    section Month 1 Details
    Week 1: API Shell & Wiring :done, 2025-03-22, 7d
    Week 2: CodeReviewAgent MVP :done, 2025-03-29, 7d
    Week 3: EthicalEngine Foundation :done, 2025-04-05, 7d
    Week 4: TestGenAgent MVP :crit, active, 2025-04-12, 7d

    section Month 2 Details
    Week 5: Basic Enforcement Logic :done, 2025-04-22, 7d
    Week 6: API Polish & Error Handling :active, 2025-04-29, 7d
    Week 7: README Documentation : 2025-05-06, 7d
    Week 8: Internal Release & Testing : 2025-05-13, 7d

    section Future Phases (Post MVP)
    Phase 2: Enhanced Features : 2025-06-22, 60d
    Phase 3: Self-Improvement & Community : 2025-08-22, 120d
```

#### Roadmap Optimization Tricks (Refined for MVP Focus) <a name="roadmap-optimization-tricks-refined-for-mvp-focus"></a>

*   **Lean & Iterative:** Focus on core MVP first.
*   **Prioritize MVP Scope:** Stick to defined MVP features.
*   **Self-Bootstrapping:** Use ecosystem tools internally.
*   **"Good Enough" for MVP:** Aim for basic, reliable functionality.
*   **Testability:** Write tests early and often.
*   **Early Feedback:** Solicit community input.

#### Beyond Month 2 (Future Iterations) <a name="beyond-month-2-future-iterations"></a>

*   Iterate on MVP feedback.
*   Implement Basic Bias Detection (Post-MVP).
*   Implement GDPR/COPPA Placeholder API (Post-MVP).
*   Plan Phase 2 features.

## Getting Started <a name="getting-started"></a>

### System Requirements <a name="system-requirements"></a>
- **Python**: 3.11+
- **Docker**: Optional, but recommended for Redis/ZAP.
- **API Keys**: Gemini (Required), Hugging Face (Optional).

### Prerequisites <a name="prerequisites"></a>

- Python 3.11+
- Docker and Docker Compose (Optional)
- Google Gemini API Key (Required)
- Hugging Face API Key (Optional)
- GitHub API Key (Optional, future use)
- OWASP ZAP API Key (Optional, advanced use)

### Installation <a name="installation"></a>

1. **Clone Repository**:
   ```bash
   git clone https://github.com/tomwolfe/metamorphic-core.git
   cd metamorphic-core
   ```
2. **Set Up Environment Variables**:
   ```bash
   cp .env.example .env
   # Modify .env with your API keys (GEMINI_API_KEY is essential)
   ```
3. **Start Redis and ZAP (Optional, Docker Compose):**
   ```bash
   # Ensure docker-compose.yml exists (copy from .example if needed)
   docker-compose up -d redis zap
   ```
4. **Set Up Virtual Environment:**
   ```bash
   python -m venv venv
   source venv/bin/activate  # Linux/macOS
   # venv\Scripts\activate     # Windows
   ```
5. **Install Dependencies:**
   ```bash
   pip install --upgrade pip
   pip install -r requirements/base.txt
   pip install -r requirements/dev.txt # Optional: for development
   pip install -e . # Install package in editable mode
   ```

### Running the API Server <a name="running_the_api_server"></a>

```bash
# Ensure virtual environment is active
python src/api/server.py
```
API accessible at `http://0.0.0.0:5000/`. Check status: `http://0.0.0.0:5000/genesis/health`.

### Quickstart Guide <a name="quickstart_guide"></a>

```bash
git clone https://github.com/tomwolfe/metamorphic-core.git && cd metamorphic-core
cp .env.example .env && nano .env # Edit .env (set GEMINI_API_KEY)
python -m venv venv && source venv/bin/activate
pip install --upgrade pip && pip install -r requirements/base.txt && pip install -r requirements/dev.txt && pip install -e .
# Optional: docker-compose up -d redis zap
python src/api/server.py & # Run in background
sleep 5 && curl http://0.0.0.0:5000/genesis/health # Test health
# Send requests to http://0.0.0.0:5000/genesis/analyze-ethical
```

## API Endpoints <a name="api-endpoints"></a>

For detailed API documentation (under development), refer to: [docs/api/api-endpoints.md](docs/api/api-endpoints.md)

| Endpoint                      | Method | Description                                                                     |
|-------------------------------|--------|---------------------------------------------------------------------------------|
| `/genesis/health`             | GET    | Check API server status.                                                        |
| `/genesis/analyze-ethical`    | POST   | Analyzes Python code for basic ethical considerations and code quality (Flake8). **MVP Core Endpoint.** |
| `/genesis/solve-math`        | POST   | Test endpoint for mathematical problem-solving.                                  |
| `/genesis/ethical/audit/{state_id}`   | GET    | Retrieve audit trail data. (Not Implemented)                                  |
| `/genesis/ethical/visualize/{state_id}` | GET    | Obtain visualization data. (Not Implemented)                                |

#### Sample MVP Request/Response - `/genesis/analyze-ethical` <a name="sample-mvp-requestresponse---genesisanalyze-ethical"></a>

**Request (Example using curl):**

```bash
curl --request POST \
  --url http://0.0.0.0:5000/genesis/analyze-ethical \
  --header 'Content-Type: application/json' \
  --data '{"code":"def hello_world():\n  print(\"Hello, world!\")"}'
```

**Response (Example - *Reflects Week 3 Completion*):**
```json
{
  "status": "success",
  "code_quality": {
    "output": "", // Flake8 output string
    "static_analysis": [] // List of parsed Flake8 issues
  },
  "ethical_analysis": {
    "policy_name": "Strict Bias Risk Policy", // Default policy used
    "description": "Zero tolerance for biased language",
    "BiasRisk": {
      "status": "compliant", // Result of basic keyword check
      "threshold": 0.1,
      "enforcement_level": 3
    },
    "TransparencyScore": {
      "status": "violation", // Result of basic docstring check
      "threshold": 0.5,
      "enforcement_level": 2
    },
    "SafetyBoundary": {
      "status": "compliant", // Result of basic unsafe op check
      "threshold": 0.8,
      "enforcement_level": 2
    }
  },
  "generated_tests_placeholder": {} // Placeholder field, populated in Week 4
}
```

#### Core API Endpoints <a name="core-api-endpoints"></a>
<details>
<summary>Phase 1 MVP API Overview</summary>

| Endpoint                          | Method | Status             | Description |
|-----------------------------------|--------|--------------------|-------------|
| **/genesis/health**               | GET    | Working            | Liveness check endpoint. |
| **/genesis/analyze-ethical**      | POST   | Alpha              | Core MVP: Code Quality (Flake8), Basic Ethics (JSON load, basic rules), Placeholder Tests (Week 4). |
| /genesis/solve-math               | POST   | Baseline           | LLM math demo endpoint. |
| /genesis/ethical/audit/{state_id} | GET    | Not Implemented    | Future ethics audit history. |
| /genesis/ethical/visualize/*      | ALL    | Not Implemented    | Future maturity visualizations. |

*Example Request (using curl):*
```bash
curl -X POST \
  http://0.0.0.0:5000/genesis/analyze-ethical \
  -H "Content-Type: application/json" \
  -d '{"code": "import os\ndef check_safety(cmd):\n if \"rm\" in cmd:\n  return False\n return True\n# No docstring"}'
```
</details>

## Contributing <a name="contributing"></a>
- **Start Contributing:** Look for **"Good First Issue"** labels. Focus on tasks in the **[Contribution Sprint Queue](#phase-1-mvp---internal-metrics-tracking)** (currently Week 4) to align with MVP goals.
- Verify implementation details against the Phase 1 MVP Roadmap Actionable Steps.

**Want visibility?** Contributor acknowledgment badge initiative planned for Phase 2.

## License <a name="license"></a>

GNU Affero General Public License v3.0 (AGPLv3). See `LICENSE`.

## License and Compliance <a name="license-and-compliance"></a>
**AGPLv3**. Designed to adhere to **OECD AI Principles**.

## Contact <a name="contact"></a>

Project inquiries: tomwolfe@gitproject.devices

## Disclaimer <a name="disclaimer"></a>

**Early MVP Development Phase - Not for Production.** Functionality is limited to Phase 1 MVP scope. **Ethical Policy Engine** supports JSON loading/validation, but **MVP enforcement uses basic rule-based checks.** Advanced ethical reasoning, full test generation, and Bandit integration are planned post-MVP.

---

## Troubleshooting <a name="troubleshooting"></a>

**Common Issues & Solutions:**

* **LLM API Key Errors:** Verify keys in `.env` and `LLM_PROVIDER` setting. Check key validity.
* **Docker Compose Issues (Redis/ZAP):** Ensure Docker is running, no port conflicts. Check logs: `docker-compose logs <service_name>`.
* **Python Dependency Errors:** Use Python 3.11+, ensure virtual environment is active. Try `pip install --upgrade pip` then reinstall requirements.
* **CI Health Check Failures:** Ensure the health check URL in `ci.yml` matches the blueprint prefix (e.g., `http://localhost:5000/genesis/health`).

## Terminology Footnotes <a name="terminology-footnotes"></a>

**Quantum-inspired analysis**: <a name="footnote-quantum-inspired"></a><sup>1</sup> Analytical methodologies inspired by quantum computing principles to explore multiple ethical risk pathways. The engine analyzes code from diverse perspectives to identify potential risks, outputting a state representing an overall ethical assessment.

---
