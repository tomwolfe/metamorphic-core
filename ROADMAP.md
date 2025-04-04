# Development Roadmap

This document outlines the development roadmap for the Metamorphic Software Genesis Ecosystem, focusing on the Phase 1 MVP and future iterations.

**🎯 CURRENT FOCUS (Week 7 - Start of Phase 2): Transition to Phase 2 - Planning & Initial Feature Enhancements - MVP RELEASED INTERNALLY ✅**

---

## Roadmap: Phase 1 MVP (Optimized for ASAP Completion) <a name="roadmap-phase-1-mvp-optimized-for-asap-completion"></a> 🚧

**Goal:** Complete the defined Phase 1 MVP (`/genesis/analyze-ethical` endpoint with a **fully JSON-configurable** Ethical Policy Engine, **Flake8 code quality**, and placeholder test generation) **this week** (by end of Week 6 - Mid-April 2025).

#### Phase 1 MVP Definition <a name="phase-1-mvp-definition"></a>

A functional API endpoint (`/genesis/analyze-ethical`) capable of:
1. Analyzing Python code for ethical concerns using a **dynamically configurable JSON policy engine** (`EthicalGovernanceEngine`).
2. Providing **Flake8 code quality assessment** (`CodeReviewAgent`).
3. Generating placeholder pytest tests (`TestGenAgent`).
4. Exposing this functionality via the API.

#### Phase 1 Deliverables <a name="phase-1-deliverables"></a>

1. Functional `/genesis/analyze-ethical` API endpoint with **dynamically configurable ethical analysis** and **Flake8 code quality checks**.
2. **Fully JSON-Configurable** `EthicalGovernanceEngine` loading policies and dynamically enforcing constraints (BiasRisk, TransparencyScore, Safety Boundary).
3. Integrated `CodeReviewAgent` providing Flake8 results within the API response.

##### Strategy Notes (MVP Focus & Simplifications) <a name="strategy-notes-mvp-focus"></a>
* **Laser Focus:** Only the **JSON-configurable `EthicalGovernanceEngine`** integration, **`CodeReviewAgent` (Flake8) integration**, and testing are blocking the MVP. Defer everything else (Bandit, SpecAnalyzer, Bias Detection).
* **Leverage Foundations:** Build on Week 1-4 work. Avoid unnecessary refactoring.
* **Self-Bootstrapping:** Use `TestGenAgent` for engine test skeletons; use `CodeReviewAgent` for code quality.
* **Parallelize:** Update docs concurrently (Week 5). Develop integration tests incrementally.
* **TDD Mindset:** Write tests early (Unit Wk4, Integration Wk5/6).
* **"Good Enough" MVP:** Focus on *correct* dynamic enforcement based on JSON and basic Flake8 reporting; sophistication can come later.
* **Intentional Simplifications:** Certain non-critical features and complex test scenarios were intentionally *commented out* or *skipped*. These are explicitly noted as `COMMENT BLOCK START` and `pytest.mark.skip(...)`. Phase 2 will re-integrate these.
* **MVP Scope - Code Quality Focus:** Phase 1 prioritized core ethical policy engine and basic *code quality* reporting via Flake8. Security scanning (Bandit, ZAP) and test generation sophistication are deferred to future phases.

#### Week 4: Configurable Ethical Engine Core - *Dynamic Policy Enforcement* <a name="week-4-configurable-ethical-engine-core---dynamic-policy-enforcement"></a> - **COMPLETE ✅** (Completed 2025-04-04)
* [✅] Task 4.1: Policy loading/validation
* [✅] Task 4.2: Dynamic enforcement logic
* [✅] Task 4.3: Engine unit tests
* [✅] Task 4.4: API endpoint updates

#### Week 5: API Integration & Testing - *Verify Dynamic Behavior* <a name="week-5-api-integration--testing---verify-dynamic-behavior"></a> - **COMPLETE ✅** (Completed 2025-04-11)
* [✅] Task 5.1: Integration tests
* [✅] Task 5.2: Error handling
* [✅] Task 5.3: Documentation updates

#### Week 6: MVP Polish & Internal Release - *Deliver & Iterate* <a name="week-6-mvp-polish--internal-release---deliver--iterate"></a> - **COMPLETE ✅** (Completed 2025-04-18)
* Task 6.1-6.4: Code review, release prep, feedback incorporation

---

## Roadmap: Phase 2 - Iteration 1 (Weeks 7-9) <a name="roadmap-phase-2---iteration-1-weeks-7-9"></a> 🚀

**Goal:** Enhance MVP capabilities through iterative improvements while establishing self-bootstrapping processes.

### Phase 2 - Iteration 1 Focus

1. **Enhanced Test Generation**:
   * Re-integrate and expand MVP test generation logic
   * Tasks include uncommenting code from `src/core/agents/test_generator.py` and re-enabling skipped tests
   * Target: Basic intelligent test generation for Python functions
   * **Estimated Time: 4 days + 0.5 day buffer**
   * **Dependency:**  None (can be started independently)
   * **Risk:** Code re-integration might introduce unexpected bugs; Logic might be more complex than anticipated.
   * **Mitigation:** Incremental re-integration, thorough unit and integration tests (add specific tests for uncommented code), code review after re-integration. **Start by writing unit tests for re-integrated logic *before* uncommenting code to proactively mitigate integration issues. Consider a brief pair programming session for re-integration to share knowledge.**
   * **DoD:**
      * Uncommented `TestGeneratorAgent` code successfully re-integrated without breaking existing functionality.
      * Skipped tests in `tests/test_test_generator.py` re-enabled and passing.
      * Test generation agent generates at least **3 basic test cases** for a sample Python function (e.g., `def square(n): return n*n`) that pass Flake8.
      * New unit tests added for re-integrated logic in `tests/test_test_generator.py`.

2. **Security Integration**:
   * Integrate ZAP security scans into `/genesis/analyze-ethical` endpoint
   * API now includes `"security_analysis"` section with ZAP findings
   * Synchronous scan implementation first, with ASYNC in Phase 2.2
   * CI pipeline dependency considerations
   * **Estimated Time: 5 days + 0.5 day buffer**
   * **Dependency:**  Requires `/genesis/analyze-ethical` endpoint to be functional (implicitly depends on MVP being stable).
   * **Risk:** ZAP integration with Flask API might be complex; Potential performance impact of synchronous scans; ZAP service reliability issues (as known from MVP).
   * **Mitigation:** Start with basic synchronous integration; Focus on API endpoint integration first, then performance optimization; Leverage CI pipeline ZAP for initial testing and reliability verification; Investigate and address local ZAP service issues if time permits (or defer to Iteration 2). **Before starting API integration, create a simple mock ZAP service for local testing to decouple API integration from real ZAP service issues. Consider a collaborative review session for the API integration design.**
   * **DoD:**
      * `/genesis/analyze-ethical` endpoint successfully triggers ZAP baseline scan **against `http://localhost:5000/genesis/health` endpoint for initial integration test.**
      * API response includes a `"security_analysis"` section with **at least a placeholder message like `"ZAP scan integration placeholder"`**.
      * Basic integration tests in `tests/integration/test_api_mvp_endpoint.py` for ZAP functionality in API endpoint (verifying presence of `"security_analysis"` section).

3. **Documentation & Refactoring**:
   * Detailed `/genesis/analyze-ethical` API documentation
   * Flake8 refinements for new code
   * README and integration test updates
   * **Estimated Time: 3 days + 0.5 day buffer**
   * **Dependency:** Can be started in parallel with feature development, but final documentation polish best done *after* features are stable.
   * **Risk:** Documentation can be time-consuming; Refactoring might uncover unexpected issues; Documentation might become outdated quickly.
   * **Mitigation:** Focus on essential API documentation first; Prioritize documentation clarity over completeness initially; Use code comments and docstrings to aid documentation; Plan for documentation updates as part of future iterations; Use Flake8 proactively during development for code quality. **Start drafting API documentation based on existing API route code *before* feature implementation is fully complete to parallelize documentation effort.**
   * **DoD:**
      * Detailed documentation for `/genesis/analyze-ethical` API endpoint documented in `docs/api/api-endpoints.md` (parameters, request/response examples, error codes, **and a section on the `code_quality` and `security_analysis` response sections**).
      * All new code in Phase 2 Iteration 1 is Flake8 compliant (no new Flake8 warnings introduced).
      * README updated with Phase 2 Iteration 1 progress and updated API endpoint details, **including a section on new features in Phase 2 Iteration 1.**
      * Integration tests in `tests/integration/test_api_mvp_endpoint.py` updated to cover new API functionality and documented in the test code comments.

#### Implementation Details

- **Test Repurposing**: Use `CodeReviewAgent` (Flake8) to validate generated test quality (ensure tests themselves are Flake8 compliant).
- **Self-Bootstrapping**: Use existing agents (CodeReviewAgent, potentially TestGenAgent) to improve new features (e.g., use TestGenAgent to generate tests for ZAP integration, use CodeReviewAgent to check generated tests).
- **Resource Allocation**: Dev 1 for Tests and Docs, Dev 2 for Security.

##### Week 9 Gantt Tasks
```mermaid
gantt
    section Phase 2 Iteration 1 Tasks (with Buffers, Dependencies & Integration)
    Test Gen - Unit Tests Pre-Work   :2025-04-21, 1d, Enhanced Test Generation
    Enhanced Test Generation         :2025-04-22, 3d, Enhanced Test Generation
    Test Gen - Re-integration Buffer  :2025-04-25, 0.5d, Enhanced Test Generation, after Enhanced Test Generation
    Security - Mock ZAP Setup       :2025-04-25, 1d, Security Agent Integration
    Security Agent Integration       :2025-04-26, 4d, Security Agent Integration
    Security - Integration Buffer     :2025-05-02, 0.5d, Security Agent Integration, after Security Agent Integration
    Docs - API Draft                :2025-04-21, 1d, Documentation
    API Endpoint Documentation        :2025-05-02, 2d, Documentation
    Docs - Documentation Buffer       :2025-05-05, 0.5d, Documentation, after API Endpoint Documentation
    Refactoring & Polish            :2025-05-05, 2d, Refactoring & Polish, after Docs - Documentation Buffer
    README Update                   :2025-05-07, 1d, README Update, after Refactoring & Polish
    **Integration & End-to-End Test**: 2025-05-08, 0.5d, Integration Test, after README Update **Code Freeze for Integration & Test: 2025-05-08**
    Iteration 1 Review & Feedback   :2025-05-08, 1d, Iteration Review, after Integration & End-to-End Test **Code Freeze for Review: 2025-05-08-05-09**
    Iteration 1 Retrospective       :2025-05-09, 0.5d, Iteration Review, after Iteration 1 Review & Feedback

    section Iteration 1 Metrics for Retrospective
    Metric 1: DoD Criteria Met?    :Iteration 1 Retrospective
    Metric 2: Time Estimation Accuracy:Iteration 1 Retrospective
    Metric 3: Major Roadblocks      :Iteration 1 Retrospective
    Metric 4: Flake8 Issue Count    :Iteration 1 Retrospective
    Metric 5: Integration Tests Added:Iteration 1 Retrospective
