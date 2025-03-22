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
   - Code quality analysis
   - Ethical compliance checks
   - Security scans
6. **Continuous Integration**: Integrate seamlessly into CI/CD pipelines
7. **Self-Improvement**: Evolve capabilities through learning and adaptation

## Current Status

The ecosystem is actively under development and currently functions as an **advanced AI-powered code analysis, ethical validation, and security scanning framework.**  While full autonomous software generation remains the long-term vision, current development is heavily focused on achieving a **Minimum Viable Product (MVP)** centered around ethical code analysis and basic code quality assessment.

**Key highlights of the current status and MVP focus:**

- **MVP Focus - API Endpoint `/genesis/analyze-ethical`:**  Current development is prioritized on delivering a functional API endpoint `/genesis/analyze-ethical`. This MVP endpoint will be capable of:
    - **Analyzing Python Code for Ethical Concerns:** Utilizing a basic Ethical Policy Engine to enforce BiasRisk, TransparencyScore, and Safety Boundary constraints (configurable via JSON policies).
    - **Providing Basic Code Quality Assessment:**  Leveraging the `CodeReviewAgent` to perform static analysis using Flake8 and report code quality issues.
    - **Generating Placeholder Tests:**  Using the `TestGenAgent` to automatically generate basic pytest placeholder tests for Python code.
    - **API Accessibility:** Providing a functional REST API endpoint for external access to ethical analysis and code quality assessment features.

- **Ethical Validation Framework (Foundation):** The foundational framework for ethical validation is in place, with initial mechanisms for policy enforcement and auditing.  The Ethical Policy Engine is under active development to enable configurable ethical constraints.

- **Code Analysis Agents (MVP Refinement):**  The `CodeReviewAgent` is being refined to provide basic code quality assessments using Flake8. The `TestGenAgent` is being streamlined to generate placeholder tests as part of the MVP feature set.

- **LLM Orchestration Layer (Core Infrastructure):** The core infrastructure for LLM orchestration is implemented, providing support for Google Gemini and Hugging Face models. This layer is being utilized for various agent functionalities, including code analysis and test generation.

- **Knowledge Graph (Backbone):**  A dynamic knowledge graph is operational, acting as a central repository for system knowledge.  Agents are being integrated to leverage the Knowledge Graph for storing and retrieving analysis data.

- **CI/CD Integration (Automated Workflows):** Automated CI workflows using GitHub Actions are established to ensure code quality and facilitate continuous integration.

- **Security Scanning (Basic Integration):** Basic integration with OWASP ZAP for dynamic application security testing (DAST) is functional, providing initial security scanning capabilities.

- **Formal Verification (Initial Phase):** Initial integration of formal verification using Coq is in place for core modules, laying the groundwork for mathematically-backed system reliability.

**Key Highlights of Current Capabilities (MVP-Focused Subset):**

- **Basic Code Analysis**: Static analysis with Flake8 via `CodeReviewAgent` for code quality insights (MVP Feature).
- **OWASP ZAP Integration**: Basic security scanning integration for web applications and APIs (Initial Capability).
- **Ethical Code Validation (Foundation)**: Foundational Ethical Policy Engine for rule-based ethical policy enforcement (MVP Feature - under development).
- **LLM Powered Features**:  Leveraging Gemini and Hugging Face models for code analysis and test generation (Core Infrastructure).
- **CI/CD Pipeline**: Automated testing and build processes via GitHub Actions (Development Infrastructure).
- **Knowledge Graph Backbone**: Centralized knowledge repository (Core Infrastructure).

**Note**: The system is currently focused on delivering the Phase 1 MVP - the `/genesis/analyze-ethical` API endpoint.  Full autonomous software generation and advanced features are planned for future phases.

## Roadmap Update (v1.5 - MVP Focus)

**Roadmap for Completion (v1.5 - MVP Focus - *Hyper-Iterative & Action-Oriented*)**

#### **Phase 1: MVP - API Endpoint `/genesis/analyze-ethical` (Next ~1-2 Months - *Prioritized & Iterative*)**

**MVP Definition:**  A functional API endpoint (`/genesis/analyze-ethical`) capable of:

1.  **Ethical Python Code Analysis:**  Analyze Python code for ethical concerns using a configurable policy engine enforcing BiasRisk, TransparencyScore, and Safety Boundary constraints, configurable via JSON policies.
2.  **Basic Code Quality Assessment:**  Leveraging `CodeReviewAgent` to run Flake8 and report output via the API.
3.  **Placeholder Test Generation:** Utilizing `TestGenAgent` to create basic pytest placeholder tests for Python code.
4.  **Functional API Access:**  Providing a functional REST API endpoint `/genesis/analyze-ethical` that integrates ethical analysis and code quality checks, returning results in JSON format.

**Phase 1 Deliverables:**
1. Functional API endpoint (`/genesis/analyze-ethical`) for ethical code analysis and basic code quality assessment, returning JSON responses.
2. Basic Ethical Policy Engine capable of loading ethical policies from JSON configurations and enforcing BiasRisk, TransparencyScore, and Safety Boundary constraints.

**Phase 1 - Gantt Chart (Estimated Timeline - Starting March 22, 2025):**

| Task Group                       | Task                                        | Week 1 (Mar 22-29) | Week 2 (Mar 29-Apr 5) | Week 3 (Apr 5-12) | Week 4 (Apr 12-19) | Week 5 (Apr 19-26) | Week 6 (Apr 26-May 3) | Week 7 (May 3-10) | Week 8 (May 10-17) |
|----------------------------------|---------------------------------------------|:------------------:|:-------------------:|:-----------------:|:-----------------:|:-----------------:|:-------------------:|:-----------------:|:-----------------:|
| **Month 1: Core & Agent Integration** | **API Endpoint & Basic Wiring**        | ████████████████████ |                      |                   |                   |                   |                    |                   |                   |
|                                  | **CodeReviewAgent MVP (Flake8)**        |                      | ████████████████████ |                   |                   |                   |                    |                   |                   |
|                                  | **EthicalPolicyEngine Foundation**     |                      |                      | ████████████████████ |                   |                   |                    |                   |                   |
|                                  | **TestGenAgent MVP & API Integration**|                      |                      |                   | ████████████████████ |                   |                    |                   |                   |
| **Month 2: MVP Polish & Enforcement**| **EthicalPolicyEngine - Enforcement**  |                      |                      |                   |                   | ████████████████████ |                    |                   |                   |
|                                  | **API Response & Error Handling**     |                      |                      |                   |                   |                   | ████████████████████ |                   |                   |
|                                  | **Documentation - MVP API**           |                      |                      |                   |                   |                   |                    | ████████████████████ |                   |
|                                  | **MVP Alpha Release & Testing**      |                      |                      |                   |                   |                   |                    |                   | ████████████████████ |

**Gantt Chart Legend:** 
- ████████████████████ = Task Duration

**Phase 1 - Higher-Level Actionable Steps:**

*   **Month 1 (Weeks 1-4): MVP API Endpoint Core & Agent Integration - *Daily Iteration*:**  Focus on getting the core API endpoint structure in place and iteratively integrating MVP versions of `CodeReviewAgent`, `EthicalPolicyEngine` (foundation), and `TestGenAgent` (placeholder tests). Daily integration testing is critical.
*   **Month 2 (Weeks 5-8): MVP API Polish & Basic Ethical Enforcement - *Weekly Iteration*:** Polish the API endpoint response, implement basic error handling, refine documentation, and implement basic constraint enforcement within the `EthicalPolicyEngine`. Prepare for an initial internal/alpha release and gather feedback.

**Phase 1 - Expanded View: Detailed Weekly Actionable Steps**

* **Month 1 (Weeks 1-4): MVP API Endpoint Core Functionality & Agent Integration - *Iterate Daily***

    *   **Week 1: MVP API Endpoint Shell & Basic Agent Wiring - *Get the API Talking to Agents***
        *   **Task 1.1: API Endpoint Route (`/genesis/analyze-ethical`) Implementation:**
            *   **Action:**  Implement the Flask API route `/genesis/analyze-ethical` in `src/api/routes/ethical_endpoints.py`. Ensure it correctly accepts POST requests with Python code provided in the `code` field of a JSON payload.
            *   **Specific Action:** Create the Flask route in `ethical_endpoints.py`.  Use Flask decorators to define it as accepting POST requests.  Implement code to extract the `code` from the incoming JSON request and return a basic JSON response like `{"status": "working"}` to confirm basic functionality.
        *   **Task 1.2: Agent Stub Integration into API Endpoint:**
            *   **Action:**  Integrate stubbed (placeholder) versions of `CodeReviewAgent` and `EthicalPolicyEngine` into the `/genesis/analyze-ethical` API endpoint.  These stubs should be instantiated within the API route handler and their core MVP methods (`analyze_python()` for `CodeReviewAgent`, `validate_code()` for `EthicalPolicyEngine`) should be called, even if they currently return placeholder data.
            *   **Specific Action:**  Instantiate `CodeReviewAgent` and `EthicalPolicyEngine` classes within the API route handler function.  Call `code_review_agent.analyze_python(code)` and `ethical_policy_engine.validate_code(code)`, even if these agent methods are currently empty or just return fixed placeholder dictionaries.
        *   **Task 1.3: Define Basic API Response Structure (JSON):**
            *   **Action:** Define and implement the basic JSON response structure for the `/genesis/analyze-ethical` endpoint according to the MVP definition.  This structure should include fields for `status`, `analysis`, `code_quality`, and `quantum_state`, even if the data for `analysis`, `code_quality`, and `quantum_state` is initially placeholder data.
            *   **Specific Action:**  Modify the API route handler to return a JSON response that conforms to the MVP defined structure.  For now, populate `analysis`, `code_quality`, and `quantum_state` fields with simple placeholder strings like `"placeholder"`.  Ensure the `status` field is dynamically set (e.g., to "working" initially).
        *   **(Daily Integration Testing - *Critical*):** **Action:** Implement minimal integration tests using `pytest` and `requests` to call the `/genesis/analyze-ethical` API endpoint daily. These tests should verify that the API endpoint is reachable, accepts POST requests, and returns a JSON response with the basic MVP defined structure (status, analysis, code\_quality, quantum\_state), even if the content is placeholder data. *Specific Action:* Create `tests/integration/test_api_mvp_endpoint.py` and add tests to validate API endpoint reachability and basic JSON response structure.  Run these tests automatically as part of your daily development workflow.

    *   **Week 2:  `CodeReviewAgent` MVP Functionality - *Flake8 Focus***
        *   **Task 2.1: `CodeReviewAgent` - Flake8 MVP Integration:**
            *   **Action:** Refine your existing `CodeReviewAgent` code to focus *exclusively* on running Flake8 and returning basic, parsed output.  Critically review the existing `CodeReviewAgent` code and comment out or skip any non-MVP functionality (like Bandit integration or advanced static analysis features) to streamline it for the MVP.
            *   **Specific Action:** Modify `CodeReviewAgent.analyze_python()` to *only* execute Flake8 via `subprocess` using the `flake8` command-line tool.  Simplify the output parsing logic to extract just the essential information: file path, line number, error code, and message from Flake8's standard output.
        *   **Task 2.2: `CodeReviewAgent` - Unit Testing (MVP - Flake8):**
            *   **Action:** Write focused unit tests specifically for the MVP-refined `CodeReviewAgent` to rigorously verify that it correctly executes Flake8 via `subprocess` and accurately parses the basic Flake8 output format.
            *   **Specific Action:** Use `pytest` and `unittest.mock` to create mock objects for `subprocess.run`.  Write unit tests in `tests/test_code_review_agent.py` to simulate various Flake8 outputs (including cases with and without errors, and different error types). Assert that the `CodeReviewAgent`'s `analyze_python()` method correctly parses these mock outputs and returns the expected structured data.
        *   **Task 2.3: API Integration - `CodeReviewAgent` MVP into Endpoint:**
            *   **Action:** Integrate the MVP-refined and unit-tested `CodeReviewAgent` into the `/genesis/analyze-ethical` API endpoint handler function. Update the API endpoint code to call the functional `CodeReviewAgent` and ensure that the `code_quality` section of the JSON API response is now populated with the actual output from the agent.
            *   **Specific Action:** Modify the API route handler in `ethical_endpoints.py` to instantiate the *functional* `CodeReviewAgent` and call its `analyze_python()` method with the code received from the API request.  Ensure the returned `code_quality` data from the agent is correctly included in the JSON API response, replacing the placeholder data.
        *   **(Daily Integration Testing - *Expand*):** **Action:** Expand the daily integration tests in `tests/integration/test_api_mvp_endpoint.py` to now specifically verify that the `code_quality` section of the API response is correctly populated with the output from the MVP `CodeReviewAgent`. Run these tests daily to ensure continuous integration of the agent with the API.

    *   **Week 3: `EthicalPolicyEngine` MVP Foundation - *JSON Policy Loading & Basic Enforcement***
        *   **Task 3.1: JSON Schema & Example Ethical Policies Definition:**
            *   **Action:** Define a robust JSON schema (`ethical_policy_schema.json`) to represent ethical policies.  Focus on the MVP-required constraints: BiasRisk, TransparencyScore, and Safety Boundary. Create *realistic example* JSON policy files that conform to this schema and define example policies for each of the MVP constraints.
            *   **Specific Action:** Create the `ethical_policy_schema.json` file in the project root directory. Within this file, define the JSON schema to structure ethical policies, including fields for `policy_name`, `description`, `constraints` (with nested objects for BiasRisk, TransparencyScore, Safety Boundary, each with fields like `threshold`, `enforcement_level`).  Create example policy JSON files (e.g., `policy_bias_risk_strict.json`, `policy_transparency_minimum.json`, `policy_safety_moderate.json`) in a new `policies/` directory in the project root. These example policies should define concrete thresholds and enforcement levels for the MVP constraints.
        *   **Task 3.2: `EthicalPolicyEngine` - Basic Loading & Enforcement Implementation:**
            *   **Action:** Implement the basic `EthicalPolicyEngine` class in `src/core/ethics/governance.py`. Focus on implementing functionality to load ethical policies from the JSON files defined in Task 3.1.  Implement a basic `enforce_policy(code, policy_config)` method that, for the MVP, provides *placeholder* enforcement logic for BiasRisk, TransparencyScore, and Safety Boundary.  Initially, this enforcement logic can be simplified (e.g., always returning "approved" or "rejected" based on a fixed policy, or using very basic rule-based checks instead of complex analysis).  *Defer database integration for policy storage; use in-memory storage for now.*
            *   **Specific Action:** Implement the `EthicalPolicyEngine` class in `governance.py`.  Create methods like `load_policy_from_json(filepath)` to load policies from JSON files based on the schema.  Implement the `enforce_policy(code, policy_config)` method. For initial MVP enforcement, this method can contain simplified placeholder logic:  For example, for BiasRisk, it could always return "policy compliant"; for TransparencyScore, it could check if the code string contains the word "transparent" and return "policy compliant" if it does, otherwise "policy violation"; and for Safety Boundary, always return "policy compliant". The key is to have *some* basic enforcement logic in place for the MVP, even if it's not sophisticated.
        *   **Task 3.3: `EthicalPolicyEngine` - Unit Testing (Loading & Basic Enforcement):**
            *   **Action:** Write unit tests for the `EthicalPolicyEngine` to rigorously verify that it can correctly load ethical policies from the JSON files defined in Task 3.1 and that the basic enforcement logic implemented in Task 3.2 (even if placeholder logic) functions as expected based on different policy configurations and code samples.
            *   **Specific Action:** Use `pytest` to create unit tests in `tests/test_ethics.py` specifically for the `EthicalPolicyEngine`.  Test cases should include: 1) Verifying that `load_policy_from_json()` correctly loads policy data from valid JSON files and raises errors for invalid files or schema violations. 2) Verifying that `enforce_policy()` method returns the expected "policy compliant" or "policy violation" results based on different policy configurations and example code inputs, according to your placeholder enforcement logic.
        *   **Task 3.4: API Integration - `EthicalPolicyEngine` Stub into Endpoint:**
            *   **Action:** Integrate the basic `EthicalPolicyEngine` (with its placeholder enforcement logic) into the `/genesis/analyze-ethical` API endpoint handler function. Modify the API endpoint code to instantiate the `EthicalPolicyEngine` and call its `enforce_policy()` method with the Python code received from the API request and a default MVP policy configuration.  Ensure that the API response now includes a placeholder `ethical_analysis` section in the JSON output.
            *   **Specific Action:** Modify the API route handler in `ethical_endpoints.py` to: 1) Instantiate the `EthicalPolicyEngine`. 2) Load a *default MVP policy configuration* (you can hardcode a simple policy JSON object directly in the API route handler for now, or load one of your example policy JSON files). 3) Call `ethical_policy_engine.enforce_policy(code, default_policy_config)`. 4) Ensure that the API response JSON now includes an `ethical_analysis` section.  For now, the `ethical_analysis` data can be placeholder information reflecting the (placeholder) enforcement results (e.g., `"status": "policy compliant/violation (placeholder)"`).
        *   **(Daily Integration Testing - *Expand*):** **Action:** Expand the daily integration tests in `tests/integration/test_api_mvp_endpoint.py` to now verify that the `ethical_analysis` section is present in the API response JSON, even if it contains placeholder data.  This confirms that the `EthicalPolicyEngine` (even in its basic form) is being called and its output is being incorporated into the API response structure.

    *   **Week 4: `TestGenAgent` MVP & API Integration - *Placeholder Tests***
        *   **Task 4.1: `TestGenAgent` - MVP Placeholder Test Generation Implementation:**
            *   **Action:** Refine your existing `TestGenAgent` code to *exclusively* focus on generating basic pytest placeholder tests.  Simplify the `generate_tests()` method to produce pytest test code that includes: 1) `import pytest` statement. 2) Test functions named `test_<function_name>_positive()` and `test_<function_name>_negative()`. 3) Within each test function, include `pytest.skip("Placeholder test - function implementation pending")` and a basic `assert True` statement.  Remove any non-MVP test generation logic to ensure it's streamlined for the MVP.
            *   **Specific Action:** Modify the `TestGenAgent.generate_tests(code, spec_analysis)` method to *only* generate the basic pytest placeholder test structure.  The `spec_analysis` input can be ignored for the MVP version. The method should return a string containing the generated pytest code.  Focus on generating *valid Python code* that includes the `pytest.skip()` markers and `assert True` placeholders.
        *   **Task 4.2: `TestGenAgent` - Unit Testing (MVP Placeholder Test Generation):**
            *   **Action:** Write unit tests specifically for the MVP-refined `TestGenAgent` to rigorously verify that its `generate_tests()` method correctly generates basic pytest placeholder test code in the expected format (including `import pytest`, test function structure, `pytest.skip()`, and `assert True`).
            *   **Specific Action:** Use `pytest` to create unit tests in `tests/test_test_generator.py` to test the `TestGenAgent`'s `generate_tests()` method.  Test cases should include: 1) Verifying that the output string contains `import pytest`. 2) Verifying that the output string contains test functions named `test_<function_name>_positive()` and `test_<function_name>_negative()`. 3) Verifying that each test function includes `pytest.skip("Placeholder test - function implementation pending")` and `assert True`.
        *   **Task 4.3: API Integration - `TestGenAgent` MVP into Endpoint:**
            *   **Action:** Integrate the MVP-refined and unit-tested `TestGenAgent` into the `/genesis/analyze-ethical` API endpoint handler function. Update the API endpoint code to call the `TestGenAgent` and, for now, *include the generated placeholder test code as a string within the JSON API response* in a new field (e.g., `"generated_tests_placeholder"`).  For the MVP, the API does *not* need to execute or run these tests, just generate and return the placeholder test code.
            *   **Specific Action:** Modify the API route handler in `ethical_endpoints.py` to: 1) Instantiate the `TestGenAgent`. 2) Call `test_gen_agent.generate_tests(code, spec_analysis)` to generate the placeholder test code. 3) Include the returned test code string in the JSON API response in a new field named `"generated_tests_placeholder"`.
        *   **(Daily Integration Testing - *Expand*):** **Action:** Expand the daily integration tests in `tests/integration/test_api_mvp_endpoint.py` to now verify that the API response JSON includes the new `"generated_tests_placeholder"` field and that this field contains a string that *looks like* basic pytest code (you can use basic string checks for keywords like `import pytest`, `def test_`, `pytest.skip`, `assert True`).  This confirms that the `TestGenAgent` is being called by the API endpoint and its generated output is being returned in the API response.

* **Month 2 (Weeks 5-8): MVP API Endpoint Polish & Basic Ethical Enforcement - *Iterate Weekly***

    *   **Week 5:  `EthicalPolicyEngine` - Basic Constraint Enforcement Logic Implementation (BiasRisk, TransparencyScore, Safety Boundary)**
        *   **Task 5.1: `EthicalPolicyEngine` - Implement Constraint Enforcement Logic:**
            *   **Action:** Replace the placeholder enforcement logic in `EthicalPolicyEngine.enforce_policy(code, policy_config)` with *basic but functional* constraint enforcement logic for BiasRisk, TransparencyScore, and Safety Boundary.  For the MVP, this logic does not need to be highly sophisticated, but it should: 1) Load constraint thresholds from the provided `policy_config` (JSON policy). 2) Implement *simple, rule-based checks* to evaluate the `code` against each constraint.  For example:
                *   **BiasRisk:**  Check if the code string contains keywords associated with bias (e.g., racial terms, gendered pronouns if relevant to your ethical policy).  If it does, consider it a "high bias risk" violation.
                *   **TransparencyScore:** Check if the code includes comments and docstrings.  Calculate a basic "transparency score" based on the presence/absence of comments and docstrings. Compare against the TransparencyScore threshold in the policy.
                *   **Safety Boundary:**  For the MVP, you can implement a very basic safety check. For example, check if the code contains potentially unsafe operations like `os.system()` or `eval()`. If it does, consider it a "safety boundary violation".
            *   **Specific Action:**  Within the `EthicalPolicyEngine.enforce_policy(code, policy_config)` method: 1) Implement logic to extract threshold values for BiasRisk, TransparencyScore, and Safety Boundary from the `policy_config` JSON object. 2) Implement the simplified, rule-based checks described above for each constraint. 3) Return a dictionary or object that clearly indicates the enforcement status (compliant/violation) for each constraint, and a overall "policy enforcement result" (APPROVED/REJECTED) based on whether any constraints were violated.
        *   **Task 5.2: `EthicalPolicyEngine` - Unit Testing (Constraint Enforcement):**
            *   **Action:** Write comprehensive unit tests for the `EthicalPolicyEngine` to rigorously verify that the constraint enforcement logic implemented in Task 5.1 functions correctly.  Test different policy configurations (with varying thresholds) and code samples that are designed to either violate or comply with each of the BiasRisk, TransparencyScore, and Safety Boundary constraints based on your simplified rule-based enforcement logic.
            *   **Specific Action:** Use `pytest` to expand unit tests in `tests/test_ethics.py` for the `EthicalPolicyEngine`.  Create test cases to: 1) Test BiasRisk enforcement: provide code samples that should and should not trigger bias risk violations based on your keyword-based check, and verify `enforce_policy()` returns the correct result for different BiasRisk thresholds in the policy. 2) Test TransparencyScore enforcement: provide code samples with varying levels of comments/docstrings, and verify `enforce_policy()` correctly assesses the transparency score and compares it to the policy threshold. 3) Test Safety Boundary enforcement: provide code samples that include and exclude unsafe operations like `os.system()` and `eval()`, and verify `enforce_policy()` correctly identifies safety boundary violations based on your check for these operations and the Safety Boundary threshold in the policy.
        *   **Task 5.3: API Integration - `EthicalPolicyEngine` Basic Enforcement into Endpoint:**
            *   **Action:** Integrate the basic constraint enforcement logic of the `EthicalPolicyEngine` into the `/genesis/analyze-ethical` API endpoint handler function. Update the API endpoint code to call `enforce_policy()` and use the returned enforcement results to dynamically set the `status` (APPROVED/REJECTED) in the JSON API response, and to populate the `ethical_analysis` section with the detailed constraint enforcement results.
            *   **Specific Action:** Modify the API route handler in `ethical_endpoints.py` to: 1) Call `ethical_policy_engine.enforce_policy(code, default_policy_config)`. 2) Use the returned "policy enforcement result" from `enforce_policy()` to set the `status` field in the JSON API response to either "APPROVED" or "REJECTED". 3) Populate the `ethical_analysis` section of the JSON API response with the detailed constraint violation/compliance information returned by `enforce_policy()`.
        *   **(Weekly Integration Testing - *Expand*):** **Action:** Expand the weekly integration tests in `tests/integration/test_api_mvp_endpoint.py` to now rigorously verify that the API endpoint correctly returns `status` (APPROVED/REJECTED) and a detailed `ethical_analysis` section in the JSON response, based on the *functional* (albeit basic) ethical policy enforcement logic you've implemented. Run these tests weekly to ensure the API endpoint and `EthicalPolicyEngine` are working together correctly.

    *   **Week 6:  API Endpoint Response Refinement & Basic Error Handling - *Polish API Output***
        *   **Task 6.1: API Response - Detailed Analysis Output Refinement:**
            *   **Action:** Refine the structure and formatting of the detailed analysis output in the API response JSON.  Specifically, improve the `code_quality` section (from `CodeReviewAgent`) and the `ethical_analysis` section (from `EthicalPolicyEngine`) to be more readable, informative, and user-friendly for the MVP.  Ensure the JSON output is well-structured and easy to parse programmatically if needed.
            *   **Specific Action:** Review the current JSON output in the `code_quality` and `ethical_analysis` sections of the API response.  Restructure and reformat this data to be more organized and easily understandable.  For `code_quality`, ensure Flake8 findings are presented clearly (file, line, code, message). For `ethical_analysis`, ensure constraint enforcement results (status for each constraint, violation details if any) are clearly presented.  Aim for a JSON structure that is both human-readable and machine-parseable.
        *   **Task 6.2: API Endpoint - Implement Basic Error Handling:**
            *   **Action:** Implement robust basic error handling within the `/genesis/analyze-ethical` API endpoint handler function. Ensure the API endpoint gracefully catches potential exceptions that might occur during agent execution (e.g., exceptions from `CodeReviewAgent.analyze_python()` or `EthicalPolicyEngine.enforce_policy()`) and returns informative JSON error responses to the client instead of crashing or returning unhandled exceptions.  Use appropriate HTTP status codes (e.g., 500 Internal Server Error for unexpected errors).
            *   **Specific Action:** Add `try...except` blocks within the API route handler function in `ethical_endpoints.py` to wrap calls to `code_review_agent.analyze_python()` and `ethical_policy_engine.enforce_policy()`.  Within the `except` blocks, implement logic to: 1) Log the error details using Flask's logging mechanism. 2) Construct a JSON error response that includes an `error` field with a descriptive error message and a `status` field set to "error". 3) Return this JSON error response to the client with a 500 Internal Server Error HTTP status code using `jsonify()` and `return ..., 500`.
        *   **Task 6.3: API Integration Testing - Response Refinement & Error Handling:**
            *   **Action:** Expand the integration tests in `tests/integration/test_api_mvp_endpoint.py` to thoroughly verify both the refined API response structure (including the improved `code_quality` and `ethical_analysis` sections) and the implemented error handling.  Specifically, add test cases to simulate error scenarios (e.g., by mocking agent methods to raise exceptions) and verify that the API endpoint correctly catches these exceptions and returns the expected JSON error responses with 500 status codes.
            *   **Specific Action:** Add integration tests to `tests/integration/test_api_mvp_endpoint.py` to: 1) Validate the refined JSON response structure, ensuring the `code_quality` and `ethical_analysis` sections are formatted as expected and contain the correct data. 2) Test error handling: Use `unittest.mock` to mock the `analyze_python()` method of `CodeReviewAgent` and the `enforce_policy()` method of `EthicalPolicyEngine` to raise exceptions.  Verify that when these exceptions are raised during API endpoint calls, the API returns a JSON error response with a 500 status code and an informative error message in the `error` field.

    *   **Week 7:  Documentation - MVP API Endpoint in `README.md` - *Basic API Usage Guide***
        *   **Task 7.1: README.md - MVP API Endpoint Documentation - *Write Usage Guide*:**
            *   **Action:** Update the `README.md` file in the project root to include comprehensive documentation for the MVP `/genesis/analyze-ethical` API endpoint.  This documentation should serve as a basic usage guide for developers or internal users who want to use the MVP functionality.  Include the following sections:
                *   **Endpoint Overview:** Briefly describe the purpose of the `/genesis/analyze-ethical` endpoint (ethical code analysis and basic code quality assessment).
                *   **Request Format:** Clearly specify the HTTP method (POST), the API endpoint URL (`/genesis/analyze-ethical`), the request headers (e.g., `Content-Type: application/json`), and the JSON request body format (including the required `code` field and its expected data type - string). Provide a clear example of a request.
                *   **Response Format:** Detail the JSON response format returned by the API endpoint.  Explain each field in the JSON response: `status` (APPROVED/REJECTED/error), `analysis` (detailed ethical analysis results - describe the structure and data), `code_quality` (code quality assessment results from Flake8 - describe the structure and data), and `generated_tests_placeholder` (placeholder test code string). Provide *example* JSON responses for both APPROVED and REJECTED scenarios, and for error scenarios.
                *   **Basic Instructions:** Include basic instructions on how to run the Flask API server locally (referencing `src/api/server.py`) and how to send requests to the `/genesis/analyze-ethical` API endpoint using `curl` or `Postman` or similar tools.
            *   **Specific Action:**  Open the `README.md` file and add a new section specifically for documenting the `/genesis/analyze-ethical` MVP API endpoint.  Write clear and concise text for each of the sections outlined above (Endpoint Overview, Request Format, Response Format, Basic Instructions).  Create well-formatted code blocks to show example requests and JSON responses.  Ensure the documentation is accurate, complete, and easy for a developer to understand and use.
        *   **Task 7.2: Documentation Review & Refinement - *Clarity and Accuracy Check*:**
            *   **Action:** Thoroughly review the updated `README.md` documentation for clarity, accuracy, completeness, and user-friendliness.  Refine the documentation based on this review to ensure it is high-quality and effectively guides users on how to use the MVP API endpoint.
            *   **Specific Action:**  After writing the initial documentation in Task 7.1, take a break and then re-read the documentation from the perspective of a developer who is new to the project and wants to use the `/genesis/analyze-ethical` API endpoint.  Check for: 1) Clarity: Is the language clear, concise, and easy to understand? Are there any ambiguous sentences or technical jargon that needs to be explained? 2) Accuracy: Is all the information technically correct? Are the request and response examples accurate and up-to-date with the current API implementation? 3) Completeness: Does the documentation cover all the essential information needed to use the API endpoint effectively (endpoint purpose, request format, response format, basic usage instructions)? 4) User-Friendliness: Is the documentation well-organized and easy to navigate? Is it presented in a logical flow that makes sense to a user trying to learn how to use the API?  Based on this review, make necessary refinements and edits to improve the overall quality of the documentation.  Ideally, ask someone else (even a colleague or fellow developer) to review the documentation and provide feedback from a fresh perspective.

    *   **Week 8:  MVP Internal/Alpha Release & Initial Testing - *First Release & Feedback***
        *   **Task 8.1:  Prepare MVP Release Package (Internal/Alpha):**
            *   **Action:** Prepare a minimal release package of the MVP for internal testing or distribution to a small group of alpha users.  This involves tagging the current codebase in Git to mark the release version, ensuring the Docker image is buildable and runnable with the MVP functionality, and preparing any necessary release notes or instructions for internal testers.
            *   **Specific Action:** 1) Use Git to tag the current commit as a release version (e.g., `git tag v0.1-alpha -m "MVP Alpha Release"` and `git push --tags`). 2) Verify that the `Dockerfile` in the project root correctly builds a Docker image that includes all the MVP functionality. Test building the Docker image locally using `docker build -t metamorphic-core-mvp-alpha .`. 3) Verify that the built Docker image is runnable and the API server starts correctly when you run it using `docker run -p 5000:5000 metamorphic-core-mvp-alpha`. 4) Prepare a brief set of release notes or instructions for internal testers. This can be a simple text file (e.g., `RELEASE_NOTES_ALPHA.md`) that includes: a summary of the MVP functionality, instructions on how to run the Docker image, instructions on how to use the `/genesis/analyze-ethical` API endpoint (referencing the `README.md` documentation), and guidance on how to provide feedback.
        *   **Task 8.2:  Conduct Internal/Alpha Testing of MVP Endpoint - *Gather Initial Usage Data*:**
            *   **Action:** Distribute the MVP release package to internal testers or a small group of alpha users and have them conduct testing of the `/genesis/analyze-ethical` API endpoint.  Provide testers with example Python code snippets to use for testing and ask them to systematically test the API endpoint's functionality based on the documentation.
            *   **Specific Action:** Share the Docker image and release notes/instructions with your internal testers or alpha users. Provide them with a set of diverse Python code snippets that represent different scenarios (ethical code, unethical code, code with code quality issues, syntactically correct code, code with syntax errors, etc.).  Ask testers to use these code snippets to send requests to the `/genesis/analyze-ethical` API endpoint, and to verify: 1) That the API endpoint is reachable and responds correctly. 2) That the API returns JSON responses in the documented format. 3) That the `status` field in the response is APPROVED/REJECTED based on the enforced policies, and that the `ethical_analysis` section breaks down violations.

* **Beyond Month 2 (Future Iterations):**  *After MVP is Functional & Stable*

    *   **Iterate on MVP Feedback:** Address feedback collected from internal/alpha testing of the MVP API endpoint.  Refine the API endpoint, ethical policy engine, and agents based on user input.
    *   **Implement Basic Bias Detection (Month 3 - if time allows):**  Integrate a *basic* bias detection library into the `BiasDetectionMitigationModule`. 
    *   **GDPR/COPPA Placeholder API (Month 3 - if time allows):** Implement the placeholder GDPR/COPPA API endpoints (`/ethical/gdpr`, `/ethical/coppa`) with clear request/response interfaces.
    *   **Phase 2 Feature Planning:** Begin more detailed planning and outlining of the enhanced features and quality improvements for Phase 2. 

**Roadmap Optimization Tricks (Refined for MVP Focus):**

* **Lean Development & Iteration:** Focus on building a functional core first and iterating rapidly based on testing and feedback. Avoid over-engineering upfront.
* **Prioritize MVP Features:**  Strictly prioritize features needed for a minimally viable product in Phase 1. Defer less critical features to later phases.
* **Self-Bootstrapping Everywhere:**  Actively leverage the Ecosystem's own capabilities (TestGenAgent, Code Review Agent) to accelerate its own development. Automate testing, code generation (stubs), and documentation where possible.
* **"Good Enough" is OK for MVP:**  For the initial MVP, focus on getting *basic* functionality working reliably.  Perfection is the enemy of "done."  Refinement and polish come later.
* **Focus on Testability:** Write tests *before* or *concurrently* with code development.  Good test coverage will speed up development and reduce bugs in the long run.
* **Consider Early Community Feedback:**  Actively seek early community feedback on the spec and roadmap *even in Phase 1* to gain valuable insights and potentially attract early contributors.  Even limited early feedback can be incredibly valuable and help refine the direction and attract initial interest.

## Getting Started

### Prerequisites

- Python 3.11+
- Docker and Docker Compose (optional)
- Google Gemini API Key
- Hugging Face API Key (optional)
- GitHub API Key (optional)

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

Modify `.env` with your API keys:

```env
LLM_PROVIDER=gemini
GEMINI_API_KEY=your_key_here
```

3. **Start Redis (optional):**

```bash
docker-compose -f docker-compose.yml.example up -d redis
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
pip install -r requirements/dev.txt
```

6. **Running the API Server**

```bash
cd src/api
python server.py
```

The API server will be available at http://0.0.0.0:50000/.

## API Endpoints

**Current Functionality (MVP - Phase 1 Focus):**

* `/genesis/analyze-ethical` (POST): **MVP Endpoint** - Analyze Python code for ethical considerations and code quality, returning a JSON report.  *(Under active development - Phase 1 MVP Deliverable)*

**Existing Endpoints (Broader Functionality - Beyond MVP):**

* `/generate` (GET): Check system status
* `/ethical/analyze` (POST): Analyze code for ethical considerations (Legacy Endpoint - Replaced by `/genesis/analyze-ethical` for MVP)
* `/ethical/solve-math` (POST): Test mathematical problem-solving (Example/Test Endpoint)
* `/ethical/audit/{state_id}` (GET): Retrieve audit trail data (Underlying Functionality)
* `/ethical/visualize/{state_id}` (GET): Obtain visualization data (Underlying Functionality)


## Contributing

Contributions are welcome. Please refer to `CONTRIBUTING.md` for guidelines.

## License

This project is licensed under the GNU Affero General Public License v3.0 (AGPLv3). See `LICENSE` for details.

## Contact

For inquiries, contact: tomwolfe@gmail.com

## Disclaimer

This project is in early development and not intended for production use. Functionality is subject to change.

## Next Optimal Step: Phase 1 MVP - Week 1 Focus 🚀

**Objective:**  Kickstart Phase 1 MVP development by establishing the foundational API endpoint structure and basic agent wiring for the `/genesis/analyze-ethical` endpoint, as outlined in **Week 1 of Month 1** of the Roadmap (v1.5).

**Context:**  Achieving a functional MVP API endpoint `/genesis/analyze-ethical` is the **top priority** for Phase 1. Week 1's tasks are crucial for setting up the core infrastructure and enabling rapid iteration. Remember: **Start Simple - Iterate Fast**.  Build a basic, functional shell *first*, then enhance. Daily integration testing is **mandatory** from Week 1 onward, enabling early issue detection and faster iteration.  **These Week 1 agent stubs are foundational for self-bootstrapping in later development phases.**

**Actionable Tasks for This Prompt (Week 1 - Month 1 MVP):**

1.  **Task 1.1: Implement API Endpoint Route (`/genesis/analyze-ethical`)**
    *   **Goal:** Create the Flask API route in `src/api/routes/ethical_endpoints.py` to handle POST requests at `/genesis/analyze-ethical`.
    *   **Specific Steps:**
        *   Open `src/api/routes/ethical_endpoints.py`.
        *   Define Flask route: `@ethical_bp.route('/genesis/analyze-ethical', methods=['POST'])`.
        *   Implement handler: `def genesis_ethical_analysis_endpoint():`.
        *   Extract `code` from JSON request: `code = request.get_json().get('code')`.
        *   Return basic JSON response: `return jsonify({"status": "working"})`.

2.  **Task 1.2: Agent Stub Integration into API Endpoint**
    *   **Goal:** Integrate placeholder `CodeReviewAgent` & `EthicalPolicyEngine` and call MVP methods within the API endpoint (returning placeholder data).
    *   **Specific Steps:**
        *   Import agents in `ethical_endpoints.py`: `from src.core.agents import CodeReviewAgent` and `from src.core.ethics.governance import EthicalPolicyEngine`.
        *   Instantiate agents in `genesis_ethical_analysis_endpoint()`: `code_review_agent = CodeReviewAgent()` and `ethical_policy_engine = EthicalPolicyEngine()`.
        *   Call MVP methods (stubbed): `code_quality_result = code_review_agent.analyze_python(code)` and `ethical_analysis_result = ethical_policy_engine.validate_code(code)`. (Create stub methods returning `{"placeholder": True}` if needed).
        *   Update API response with placeholders: `return jsonify({"status": "working", "code_quality": "placeholder", "ethical_analysis": "placeholder"})`.

3.  **Task 1.3: Define Basic API Response Structure (JSON)**
    *   **Goal:** Ensure API returns JSON response with MVP structure: `status`, `analysis`, `code_quality`, `quantum_state`.
    *   **Specific Steps:**
        *   Review MVP response structure: `{"status": "...", "analysis": "...", "code_quality": "...", "quantum_state": "..."}`.
        *   Modify `jsonify()` in `genesis_ethical_analysis_endpoint()` to strictly adhere to this structure.
        *   Populate `analysis` & `quantum_state` with placeholders: `"placeholder"`.

4.  **Daily Integration Testing (Mandatory)**
    *   **Goal:** Implement daily integration tests to verify API endpoint and JSON response structure.
    *   **Specific Steps:**
        *   Create `tests/integration/test_api_mvp_endpoint.py`.
        *   Use `pytest` and `requests`.
        *   Write tests to:
            *   POST request to `http://localhost:5000/genesis/analyze-ethical` (`{"code": "print('hello')"}`).
            *   Assert 200 status code.
            *   Assert valid JSON response.
            *   Assert JSON contains fields: `"status"`, `"analysis"`, `"code_quality"`, `"quantum_state"`.
        *   Run tests **daily** after code changes.

**Guiding Principles for Week 1:**

*   **Start Simple:** Focus on basic API structure and wiring.
*   **Iterate Fast:**  Small changes, frequent testing.
*   **Daily Integration Tests:** Run tests daily for continuous validation.
*   **"Placeholder" is OK (MVP Foundation):**  Placeholder agent outputs are expected in Week 1.

**Expected Outcome (End of Week 1 Checklist):**

*   [ ] Functional `/genesis/analyze-ethical` API endpoint (Flask).
*   [ ] Basic wiring to stubbed `CodeReviewAgent` & `EthicalPolicyEngine`.
*   [ ] API returns MVP JSON response structure (with placeholders).
*   [ ] Automated daily integration tests (verifying API & JSON structure).

**Next Steps (After Week 1):**  Proceed to **Week 2 of Month 1**, focusing on **implementing Flake8 integration in `CodeReviewAgent`** to provide basic code quality assessment for the MVP API endpoint.

**Let's begin building the foundation for the Metamorphic Software Genesis Ecosystem MVP!**
