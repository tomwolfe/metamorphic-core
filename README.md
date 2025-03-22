# Metamorphic Software Genesis Ecosystem 🚀

[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-AGPLv3-blue.svg)](LICENSE)

**Version ∞: An Ever-Evolving Framework for Software Excellence**

**Driven by AI and guided by a comprehensive high-level specification and roadmap, the Metamorphic Software Genesis Ecosystem is redefining software development through self-evolving, ethical, and secure solutions.**

## Vision

To create a self-refining, AI-driven framework capable of independently generating, maintaining, and evolving high-quality software solutions, operating as a perpetual engine of innovation and improvement.

## Key Objectives

- **Autonomous Software Development**: Enable independent creation of complete software applications from high-level specifications
- **Ethical Assurance**: Integrate robust ethical governance to ensure compliance with defined principles
- **Continuous Quality**: Automate testing, code review, and security analysis
- **Self-Enhancement**: Enable the ecosystem to learn, adapt, and improve through feedback

## Envisioned Workflow: From Concept to Code

1. **User Input**: Provide a high-level description of the desired software in natural language or via a future cloud interface
2. **Specification Refinement**: AI agents enhance input, clarifying ambiguities and identifying potential issues
3. **Design & Planning**: Generate a comprehensive software architecture
4. **Code Generation**: Produce code across multiple languages, adhering to best practices
5. **Testing & Validation**: Conduct thorough testing, including:
   - Unit, integration, and end-to-end tests
   - Code quality analysis with Flake8
   - Ethical assessment using rule-based engine and quantum-inspired analysis
   - Security scans with OWASP ZAP and Bandit
6. **Continuous Integration**: Integrate seamlessly into CI/CD pipelines using GitHub Actions
7. **Self-Improvement**: Evolve capabilities through learning and adaptation

## Current Status

The ecosystem is actively under development and demonstrating core functionalities as an **advanced AI-powered code analysis, ethical validation, and security scanning framework.** While full autonomous software generation is still under development, the current status showcases significant progress in key areas:

- **Ethical Validation Framework**: Mechanisms for ethical assessment are in place, leveraging a rule-based engine and quantum-inspired state analysis for ethical insights.  Policy configuration via JSON is under development.
- **Code Analysis Agents**: Code review capabilities are implemented using static analysis tools like Flake8 and Bandit, providing detailed code quality and security vulnerability assessments. Basic pytest placeholder test generation is implemented but not yet fully integrated into the API workflow.
- **Managing Long AI Contexts**: Initial mechanisms for managing long AI contexts through smart LLM selection, context chunking, and summarization are implemented.
- **LLM Orchestration Layer**: Robust infrastructure for managing interactions with multiple LLMs, currently supporting Google Gemini and Hugging Face models. The system intelligently routes tasks, manages context, and optimizes costs. Phase 1.4 development is ongoing, with focus on enhanced context management and ethical policy engine integration.
- **Knowledge Graph**: A dynamic knowledge graph is operational, serving as a central repository for ethical principles, code analysis findings, security vulnerabilities, and system knowledge, enabling informed decision-making and continuous learning.
- **CI/CD Integration**: Automated CI workflows using GitHub Actions are established, ensuring code quality, running tests (including generated tests), performing security scans, and building Docker images upon code changes.
- **Security Scanning**: Integration with OWASP ZAP for dynamic application security testing (DAST) is functional, enabling baseline scans to detect web application vulnerabilities, particularly for APIs. The system actively scans API endpoints and reports high-risk issues. Baseline security scanning with Bandit is also integrated.
- **Formal Verification**: Initial integration of formal verification using Coq is in place, with compiled proofs included in the CI pipeline, starting with core modules like boundary detection.

**Key Highlights of Current Capabilities:**

- **Advanced Code Analysis**: Static analysis with Flake8 and Bandit, providing detailed code quality and security insights accessible via API.
- **OWASP ZAP Integration**: Automated security scanning for web applications and APIs, with vulnerability reporting and scan history caching.
- **Ethical Code Assessment**: Rule-based ethical assessment engine with quantum-inspired analysis providing ethical insights on code. Policy configuration via JSON is under development.
- **LLM Powered Features**:  Leveraging Gemini and Hugging Face models for code analysis, test generation (placeholder tests), and problem-solving.
- **CI/CD Pipeline**: Automated testing, security scanning, and build processes via GitHub Actions, including Coq proof compilation.
- **Knowledge Graph Backbone**: Centralized storage and retrieval of system knowledge, analysis data, and ethical guidelines.

**Note**: While the system is not yet capable of fully autonomous software generation, it currently functions as an advanced AI-powered code analysis and ethical assessment framework with basic security scanning capabilities.

## Roadmap Update (v1.3)

**Roadmap for Completion (Optimized for Existing Codebase - Iterative MVP Approach)**

#### **Phase 1: MVP - Refine Existing Core (Next ~3 Months) - *Leverage & Focus***

**Key Principle:** *Phase 1 is about *refining and focusing your existing codebase* to meet the MVP definition, not starting from scratch. We use your current agents as a *starting point* for the "barebones" implementations.*

---

**Phase 1 MVP Definition:**  A functional API endpoint (`/genesis/analyze-ethical`) capable of:

1.  **Analyzing Python Code for Ethical Concerns:** Using a configurable policy engine (enforcing BiasRisk, TransparencyScore, and Safety Boundary constraints, configurable via JSON).
2.  **Providing Basic Code Quality Assessment:**  Leveraging `CodeReviewAgent` (Flake8 output reporting via API).
3.  **Generating Placeholder Tests:** Utilizing `TestGenAgent` to create basic pytest placeholder tests for Python code.
4.  **API Access:**  Providing a functional `/genesis/analyze-ethical` API endpoint that integrates ethical analysis and code quality checks.

---

**Phase 1 Deliverables:**
1. Functional API endpoint (`/genesis/analyze-ethical`) for ethical code analysis.
2. Basic Ethical Policy Engine enforcing BiasRisk, TransparencyScore, and Safety Boundary constraints, with policies configurable via JSON.

**Phase 1 Actionable Steps (Version 1.3 - Revised 3 - *Final Revision*)**

* **Month 1: Refine Agents & Ethical Engine Foundation**
    1.  **Refine TestGenAgent:** Integrate into API endpoint workflow, add unit tests.

        <details>
        <summary><b>Example LLM Prompt for Task 1: Refine TestGenAgent</b></summary>

        ```text
        ## Task: Refine TestGenAgent for Phase 1 MVP - API Integration and Unit Tests

        **Context:**

        You are an AI assistant helping to develop the Metamorphic Software Genesis Ecosystem, an open-source project for AI-driven software development.  The project is currently in Phase 1 MVP development.

        **Goal:**

        Refine the existing `TestGenAgent` to meet the Phase 1 MVP requirements, specifically:

        1.  **Integrate `TestGenAgent` into the `/genesis/analyze-ethical` API endpoint workflow.**  Currently, the API endpoint in `src/api/routes/ethical_endpoints.py` performs code quality analysis and basic ethical validation but does not use the `TestGenAgent`.  The refined agent should be called within this endpoint's flow. For MVP, even a basic integration to confirm it's called and its output is reflected in the API response (e.g., a confirmation message) is sufficient.
        2.  **Add or update unit tests for the refined `TestGenAgent` in `tests/test_test_generator.py`.** Ensure the tests validate the MVP-level functionality of the agent, especially its ability to generate basic pytest placeholder tests and its API endpoint integration (if applicable at unit test level).

        **Phase 1 MVP Definition (from Roadmap):**

        A functional API endpoint (`/genesis/analyze-ethical`) capable of:

        1. Analyzing Python Code for Ethical Concerns: Using a configurable policy engine...
        2. Providing Basic Code Quality Assessment: Leveraging `CodeReviewAgent`...
        3. **Generating Placeholder Tests:** Utilizing `TestGenAgent` to create basic pytest placeholder tests for Python code.
        4. API Access: Providing a functional `/genesis/analyze-ethical` API endpoint...

        **Phase 1 Deliverable (Relevant to this task):**

        * Functional API endpoint (`/genesis/analyze-ethical`) for ethical code analysis (needs to include basic TestGenAgent functionality).

        **Phase 1 Actionable Step (Relevant to this task - Month 1, Step 1):**

        * **Refine TestGenAgent:** Integrate into API endpoint workflow, add unit tests.

        **High-Level Specification (Relevant Principles):**

        * **Continuous Quality**: Automate testing...
        * **Self-Enhancement**: Enable the ecosystem to learn, adapt, and improve through feedback (testing provides feedback).

        **Current Codebase (Relevant Files - Please analyze and modify these code blocks. **IMPORTANT:** Replace the `[PASTE CODE HERE]` placeholders below with the *actual content* of each file before submitting this prompt to the LLM):**

        *   **`src/core/agents/test_generator.py` (Current `TestGenAgent` code):**
            ```python
            [PASTE CODE HERE - Content of src/core/agents/test_generator.py]
            ```

        *   **`src/api/routes/ethical_endpoints.py` (API endpoint - `/genesis/analyze-ethical`):**
            ```python
            [PASTE CODE HERE - Content of src/api/routes/ethical_endpoints.py]
            ```

        *   **`tests/test_test_generator.py` (Existing `TestGenAgent` tests):**
            ```python
            [PASTE CODE HERE - Content of tests/test_test_generator.py]
            ```

        **Instructions:**

        1.  **Analyze the provided code files and the roadmap/specification context.**
        2.  **Modify `src/core/agents/test_generator.py` (if needed) to ensure it is ready for MVP API integration.** For MVP, focus on basic placeholder test generation.  Do *not* implement more advanced test generation features yet (defer to later phases).
        3.  **Modify `src/api/routes/ethical_endpoints.py` to integrate the `TestGenAgent` into the `/genesis/analyze-ethical` endpoint workflow.**  Call the `TestGenAgent` after code quality and ethical analysis within the endpoint's function. For MVP, simply ensure the agent is called and some indication of its execution (even a basic message in the API response confirming test generation) is present.  The generated tests themselves do not need to be returned via the API in this MVP phase.
        4.  **Add or update unit tests in `tests/test_test_generator.py` to validate the refined `TestGenAgent` and its core MVP functionality.** Ensure tests cover the agent's ability to generate basic pytest placeholder tests and its integration into the API endpoint workflow (if applicable at the unit test level).  Unskip any relevant tests and add new ones as needed.
        5.  **Return the modified code. **For each modified file, please clearly indicate the changes you made, ideally in a diff-like format.  For example, if you modify `src/core/agents/test_generator.py`, your response should include output similar to this (showing added lines with `+`, removed with `-`):**

            ```diff
            --- a/src/core/agents/test_generator.py
            +++ b/src/core/agents/test_generator.py
            @@ -10,5 +10,6 @@
             class TestGenAgent:
                 def __init__(self):
                     self.llm = LLMOrchestrator()
            +        self.api_integrated = True  # Example change - added a new line

                 def generate_tests(self, code: str, spec_analysis: dict) -> str:
                     # ... rest of the code ...
            ```

            **Return the full content of each modified file along with these diff-like change indications. If you made changes to other files, please include those as well with change indications.**

        **Key Considerations for MVP:**

        *   **Focus on basic placeholder test generation.** Sophisticated test generation is deferred to later phases.
        *   **Prioritize API integration.** Make sure the agent is called within the API endpoint flow and its execution is confirmed in the API response (even minimally).
        *   **Keep it simple and functional for MVP.**  "Good enough" is OK for MVP. Refinement and polish come later.
        *   **Leverage existing code and tests as much as possible.**

        Let's work iteratively to refine the `TestGenAgent` and achieve this MVP task!
        ```

        </details>

    2.  **Refine CodeReviewAgent:** Verify API integration, update unit tests.
    3.  **Design JSON Schema:** Create `ethical_policy_schema.json` file.
    4.  **Implement Ethical Policy Engine:** JSON configuration loading, basic enforcement, unit tests.
    5.  **GDPR/COPPA Placeholder API:** Verify API routes, document interfaces.
    6.  **Bias Detection Module:** Integrate starter library, basic text analysis.
* **Month 2: Integrate Agents & API Endpoint**
    1.  **Integrate Specification Analysis Agent:** API endpoint integration, JSON output, basic ethical engine use.
    2.  **Refine API Endpoint (`/genesis/analyze-ethical`):**
        *   **2a. Orchestrate Agents:** Integrate `CodeReviewAgent`, `EthicalPolicyEngine`, `SpecificationAnalyzer`, `BiasDetectionMitigationModule`.
        *   **2b. Format JSON Response:** Structure output from agents and engine into MVP-defined JSON format.
        *   **2c. Integration Tests:** Write integration tests for the complete `/genesis/analyze-ethical` endpoint flow.
    3.  **(Step Removed - Redundant)**
    4.  **CI/CD Integration:** Extend CI pipeline for MVP endpoint integration tests.
* **Month 3: MVP Refinement & Documentation**
    1.  **Polish MVP API Endpoint:** Refine error handling, response formatting, performance.
    2.  **Document MVP API Endpoint:** Update `README.md` with usage instructions, examples.
    3.  **Initial MVP Release:** Prepare minimal MVP release, update `INSTALL.md`/`README.md`.
    4.  **Gather MVP Feedback:** Collect feedback from internal/alpha testers.

<details>
<summary><b>Internal Metrics Tracking Table - Phase 1 MVP Development</b></summary>

| Roadmap Item                                  | Effort Completed (Dev %) | Functionality Validated (MVP %) | Status (Roadmap) | Next Steps                                                                                                                              |
| :-------------------------------------------- | :-----------------------: | :-----------------------------: | :--------------- | :-------------------------------------------------------------------------------------------------------------------------------------- |
| MVP Deliverable 1: API Endpoint              |            90%            |               85%               | Implemented      | 1. Write integration tests 2. Polish error handling                                                                                   |
| MVP Deliverable 2: Configurable Policy Engine |            50%            |               20%               | Partially Implemented | 1. Design `ethical_policy_schema.json` 2. Implement JSON loading in `EthicalPolicyEngine` 3. Implement `/ethical/policy/load` endpoint 4. Implement `/ethical/policy/view` endpoint |
| TestGenAgent Refinement                       |            80%            |               50%               | Partially Implemented | 1. Integrate into API workflow 2. Activate in endpoint 3. Write integration tests                                                                    |
| CodeReviewAgent Refinement                      |            95%            |               90%               | Implemented      | 1. Write integration tests (if needed) 2. Minor polish                                                                                       |
| JSON Schema Design                             |             0%            |                0%               | Not Implemented  | 1. Design and create `ethical_policy_schema.json` file                                                                                     |
| Ethical Policy Engine (JSON Configurable)      |            30%            |                5%               | Not Implemented  | 1. Implement JSON loading 2. Implement `/ethical/policy/load` endpoint 3. Implement `/ethical/policy/view` endpoint 4. Integrate into workflow 5. Write tests 6. MVP constraints |
| GDPR/COPPA Placeholder API                     |            70%            |               60%               | Partially Implemented | 1. Document API endpoints in README/Swagger                                                                                            |
| Bias Detection Module Integration             |            20%            |               10%               | Not Implemented  | 1. Integrate starter bias detection library 2. Basic text analysis 3. Placeholder integration in workflow                                 |
| **API Endpoint Integration Task**              |            60%            |               50%               | Partially Implemented | 1. Refine agent orchestration 2. Implement JSON response formatting 3. Write integration tests                                                            |

</details>

## Getting Started

### Prerequisites

- Python 3.11+
- Docker and Docker Compose (optional, for Redis and ZAP)
- Google Gemini API Key (Required for Gemini LLM Provider)
- Hugging Face API Key (Optional, for Hugging Face LLM Provider)
- GitHub API Key (Optional, for future GitHub integrations)
- OWASP ZAP API Key (Optional, for running ZAP security scans)

### Installation

1. **Clone the Repository**:

```bash
git clone https://github.com/tomwolfe/metamorphic-core.git
cd metamorphic-core
```

2. **Set Up Environment Variables**:

```bash
cp .env.example .env
```

Modify `.env` with your API keys and desired configurations.  Ensure you set at least `GEMINI_API_KEY` if using the default Gemini LLM provider.

```env
LLM_PROVIDER=gemini # or huggingface
GEMINI_API_KEY=your_key_here
# HUGGING_FACE_API_KEY=your_hf_api_key # Required if LLM_PROVIDER=huggingface
# YOUR_GITHUB_API_KEY=your_github_token # Optional
# ZAP_API_KEY=your_zap_api_key # Optional
# DOCKERHUB_USERNAME=your_dockerhub_username # Optional

# System configuration (adjust as needed)
SAFETY_MARGIN=5
QUANTUM_DEPTH=3
ETHICAL_THRESHOLD=90
PYTHONPATH=./src
```

3. **Start Redis and ZAP (Optional, using Docker Compose):**

If you want to use Redis for caching or run OWASP ZAP security scans locally, you can start these services using Docker Compose:

```bash
docker-compose -f docker-compose.yml.example up -d redis zap
```

4. **Set Up Virtual Environment:**

```bash
python -m venv venv
source venv/bin/activate  # Linux/macOS
venv\Scripts\activate     # Windows
```

5. **Install Dependencies:**

```bash
pip install --upgrade pip
pip install -r requirements/base.txt
pip install -r requirements/dev.txt # Optional: for development dependencies (testing, linting)
```

6. **Running the API Server**

```bash
cd src/api
python server.py
```

The API server will be available at http://0.0.0.0:50000/.

## API Endpoints

**Current Functionality (Phase 1 MVP):**

* `/genesis/health` (GET): Check API server status, returns `{"status": "ready"}` if the server is running.
* `/genesis/analyze-ethical` (POST): Analyze Python code for basic code quality (Flake8) and ethical considerations (basic assessment). **This is the core MVP endpoint.**
    *   **Request Body (JSON):** `{"code": "YOUR_PYTHON_CODE_HERE"}`
    *   **Response (JSON):**
        ```json
        {
          "status": "working",
          "code_quality": "flake8_output_or_no_result",
          "analysis": "ethical_analysis_status_or_no_result",
          "quantum_state": "placeholder"
        }
        ```
* `/genesis/solve-math` (POST): Test endpoint for mathematical problem-solving (basic test).
* `/genesis/ethical/audit/{state_id}` (GET): Retrieve audit trail data for a given `state_id` (not yet fully implemented).
* `/genesis/ethical/visualize/{state_id}` (GET): Obtain visualization data for a given `state_id` (not yet fully implemented).

**Note:**  The API functionality is currently focused on the `/genesis/analyze-ethical` endpoint as part of the Phase 1 MVP.  Other endpoints are for testing or represent future functionality.

## Contributing

Contributions are welcome, especially to help us reach our Phase 1 MVP goals! Please refer to `CONTRIBUTING.md` for guidelines (Contribution guidelines are under development).

## License

This project is licensed under the GNU Affero General Public License v3.0 (AGPLv3). See `LICENSE` for details.

## Contact

For inquiries, contact: tomwolfe@gmail.com

## Disclaimer

**This project is in early MVP development and not intended for production use.** Functionality is limited to the features outlined in the Phase 1 Roadmap and is subject to change. API endpoints and responses are under active development and may evolve.  **We are actively working towards the Phase 1 MVP outlined in the Roadmap below.**
