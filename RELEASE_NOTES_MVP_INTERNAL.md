**Metamorphic Software Genesis Ecosystem - Phase 1 MVP Internal Release (v0.1.0-internal-mvp) - QUICK START GUIDE**

**Roadmap Update - Phase 2 Iteration 1 Focus:** <--- UPDATED SECTION HEADING
Following the internal MVP release and the successful completion of **Phase 1.5: Workflow Automation Side Project** and **Phase 1.6: Enhanced Workflow Automation**, we are now transitioning into the next phase, **Phase 2 Iteration 1: Resilient Workflow & Automated Remediation**. See [ROADMAP.md](ROADMAP.md) for the updated roadmap and details on Phase 2 Iteration 1.

**Key Features (MVP Highlights):**

*   **Code Analysis (Flake8):** Static analysis integrated into `/genesis/analyze-ethical` API. **Verified and functional.**
*   **Security Scanning (ZAP - CI Pipeline Only):** Automated DAST via OWASP ZAP in CI pipeline. **Local ZAP in `docker-compose.yml` is NOT reliably functional in this MVP release - use CI reports for security scans.**
*   **Ethical Assessment:** JSON-configurable `EthicalGovernanceEngine` with policy enforcement. **API integration tested and refined.**
*   **API Endpoint (`/genesis/analyze-ethical`):** Core functionality (Ethics + Flake8 Quality) integrated and verified.
*   **Automated Workflow Initiation Script (`dev_run.py`):** Added a helper script (`dev_run.py`) to automate restarting the `metamorphic-core` Docker service and initiating the automated workflow via the CLI. This simplifies the developer setup for running the autonomous loop. **(Completed as part of Phase 1.7 Task 1)**

**Known Issues & Limitations (MVP Scope):**

*   **Local ZAP Service Issue:** ZAP in `docker-compose.yml` is **not reliable locally.** Use CI pipeline ZAP reports for security findings. **Flake8 code quality checks are functional locally.**
*   **Placeholder Test Generation:** `TestGenAgent` generates placeholder tests only. **No meaningful test coverage.**
*   **Limited API Endpoints:** MVP focuses on `/genesis/analyze-ethical`. Other API endpoints are placeholders.
*   **Performance:** Latency may be observed, especially with LLM features. **Flake8 code quality checks are efficient.**
*   **Documentation (In-Progress):** Detailed API docs and contribution guidelines are still under development.

**Feedback Requested (Priority Areas):**

1.  **Functionality of `/genesis/analyze-ethical` Endpoint:**
    *   Does it function as expected?
    *   Ethical violation detection accurate?
    *   Flake8 code quality reporting accurate?
    *   API responses clear?

2.  **Dynamic Policy Enforcement:**
    *   Does the Ethical Governance Engine dynamically enforce policies?
    *   Test different policies (e.g., `policy_bias_risk_strict.json`).
    *   Verify `ethical_analysis` section in API response.
    *   Do policy violations result in `"status": "rejected"`?

3.  **Code Quality Reporting (Flake8 Integration):**
    *   Are Flake8 messages clear and informative?

4.  **Usability & General Impressions:**
    *   "Getting Started" instructions clear?
    *   `/genesis/analyze-ethical` API easy to use? Request/response format intuitive?
    *   JSON policy format understandable?
    *   Overall MVP impression? Most promising aspects? Areas for improvement?

**Getting Started - Quickstart for Internal Testers:**

*   **Follow "Getting Started" in `README.md` for Prerequisites & Installation.**
*   **Run API Server:** `python src/api/server.py`
*   **Test `/genesis/analyze-ethical` Endpoint:**
    *   Use `curl` or Postman to send POST requests to `http://127.0.0.1:5000/genesis/analyze-ethical`.
    *   Example Request Body (JSON):
        ```json
        {"code": "import os # F401\ndef add(a, b):\n  return a + b"}
        ```
    *   Examine `"code_quality"` and `"ethical_analysis"` sections in the API response.
    *   (Optional) Test different policies by specifying `"policy_name"` in the request body.

**Provide Feedback:**

*   **Method:** [Specify Feedback Method - e.g., create issues in GitHub, post in #metamorphic-core-internal Slack channel]
*   **Include:** Steps to reproduce issues, code snippets/API requests, screenshots (if helpful), suggestions for improvement.

**Important Notes:**

*   **MVP Status - Not Production Ready.**
*   **API Stability:** API endpoints may change in future releases.