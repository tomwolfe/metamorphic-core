# 🌟 Metamorphic Software Genesis Ecosystem  
[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml)  
[![License](https://img.shields.io/badge/License-AGPLv3-blue.svg)](LICENSE)  
[![Roadmap Status](https://img.shields.io/badge/Roadmap-Phase_2_Iteration_2-yellowgreen)](ROADMAP.md)  

**🎯 CURRENT FOCUS: Phase 2 Iteration 2 - Enhanced Agents & Knowledge Graph 🧠**  
*Revolutionizing AI-Driven Software Development Through Autonomy, Ethics, and Self-Improvement*

---

## 📘 Overview  
The **Metamorphic Software Genesis Ecosystem (MSGES)** is an advanced AI framework designed to autonomously generate, maintain, and evolve secure, ethical, and high-performance software solutions from high-level specifications. Built on cutting-edge LLM orchestration and formal verification principles, MSGES combines workflow automation, ethical governance, and continuous self-improvement to redefine modern software development.

### ✨ Key Features  
- **Autonomous Code Generation**: Build applications from natural language specs.  
- **Ethical Governance**: Enforce customizable policies for bias mitigation, transparency, and compliance.  
- **Automated Validation & Remediation**: Integrated testing, security scans (OWASP ZAP), and code reviews, with automated self-correction attempts for common failures.  
- **Knowledge Graph Integration**: Neo4j-powered context management for smarter code generation.  
- **Self-Improving Workflows**: Learn from feedback, metrics, and past iterations to optimize processes.  

> *“A self-driving development platform for the next era of software engineering.”*  

---

## 🚀 Getting Started  

### 🔧 Prerequisites  
- **Python 3.11+** (`python --version`)  
- **Git** (`git --version`)  
- **Docker Desktop** (recommended for Redis/ZAP services)  
- **API Keys**: Gemini, Hugging Face, GitHub (optional).  

### 📦 Installation  
```bash
# Clone the repository
git clone https://github.com/tomwolfe/metamorphic-core.git && cd metamorphic-core

# Set up environment variables
cp .env.example .env
# Edit `.env` with your API keys (see below)

# Start Redis & OWASP ZAP (via Docker)
docker-compose up -d redis zap

# Set up virtual environment
python -m venv venv
source venv/bin/activate  # Linux/macOS
# venv\Scripts\activate    # Windows

# Install dependencies
pip install -r requirements/base.txt
pip install -r requirements/dev.txt  # Optional: dev tools (Flake8, pre-commit)
```

#### 🛡️ .env Configuration  
1. Copy `.env.example` → `.env`.  
2. Required: `GEMINI_API_KEY` (from [Google AI Studio](https://ai.google.dev/)).  
3. Optional: Set `HUGGING_FACE_API_KEY`, `YOUR_GITHUB_API_KEY`, and `ZAP_API_KEY`.  

> ⚠️ **Never commit `.env` to version control!** Add it to `.gitignore`.

---

## 🏁 Running the API Server  
```bash
# Start the server
python src/api/server.py

# Check health endpoint
curl http://127.0.0.1:5000/genesis/health
```

---

## 🧪 Quickstart: Ethical Code Analysis  
Test the core API with a sample Python function:  
```bash
curl -X POST http://127.0.0.1:5000/genesis/analyze-ethical \
  -H "Content-Type: application/json" \
  -d '{"code": "def calculate_area(radius):\n    \"\"\"Calculates the area of a circle.\"\"\"\n    if radius < 0:\n        raise ValueError(\"Radius cannot be negative\")\n    return 3.14159 * radius * radius"}'
```

---

## 🔄 Automated Workflow (Post-Phase 1.7)  
The primary way to run the automated development workflow is now using the `dev_run.py` helper script. This script handles restarting the necessary Docker services (like `metamorphic-core`) and then calling the main CLI entry point to initiate the autonomous loop.

1.  **Ensure the API server is running:** While `dev_run.py` attempts to restart the `metamorphic-core` service, it's good practice to ensure Docker is running and the service is available.
2.  **Prepare `ROADMAP.json`**: Ensure your `ROADMAP.json` file is correctly formatted and contains at least one task with the status `"Not Started"`. The Driver will automatically select the first such task it finds.
3.  **Run the development runner script**:  
    ```bash
    python dev_run.py  # Restarts docker service and auto-triggers `/genesis/drive_workflow` via CLI
    ```
    *   *(Optional)* Specify a different roadmap file: `python dev_run.py --roadmap path/to/your/roadmap.json`
    *   *(Optional)* Specify an output directory: `python dev_run.py --output-dir ./my_output`
4.  **Monitor logs**: View validation results, grade reports, and roadmap updates in the API server terminal.  

---

## 🌐 Core API Endpoints  
| Endpoint                  | Method | Description                          |
|--------------------------|--------|--------------------------------------|
| `/genesis/health`        | GET    | Health check for the API server.     |
| `/genesis/analyze-ethical` | POST  | Analyze code for ethics/code quality.|
| `/genesis/drive_workflow`| POST   | Trigger autonomous workflow loop.    |

---

## 🛠️ Technical Highlights  
- **LLM Providers**: Gemini (default), Hugging Face.  
- **Knowledge Graph**: Planned integration with Neo4j for semantic context.  
- **Security**: OWASP ZAP + Bandit for DAST/SAST.  
- **Formal Verification**: Coq/Isabelle/Z3 integrations.  
- **Ethics Engine**: AST-based policy enforcement, bias detection.  

---

## 📈 Roadmap & Progress  
**Phase 1.7 COMPLETED**: Resilient Workflow & Automated Remediation (Automated remediation for tests, code style, ethics; dependency scheduling).

**Phase 2 Iteration 2 IN PROGRESS**: Enhanced Agents & Knowledge Graph (Advanced AI planning, RL for agent optimization, deeper KG integration).  
See the full roadmap in [`ROADMAP.md`](ROADMAP.md).  

---

## 🤝 Contributing  
We welcome contributors! Please read our [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.  

---

## 📚 Documentation  
- [SPECIFICATION.md](SPECIFICATION.md): Full architectural vision.  
- [WORKFLOWS GUIDE](docs/workflows/markdown_automation.md): Detailed automation workflows.  
- [COMPETITIVE LANDSCAPE](COMPETITIVE_LANDSCAPE.md): Industry comparison.  

---

## 🛠️ Troubleshooting  
- **Docker Issues**: Ensure Docker Desktop is running.  
- **API Key Errors**: Double-check `.env` entries.  
- **Workflow Failures**: Review grade reports and server logs.  

---

## 📄 License  
This project is licensed under the [AGPLv3 License](LICENSE).  

---

## 📬 Contact  
For questions or collaboration, open an issue on GitHub or email [tomwolfe@gmail.com].  

---

## ⚠️ Disclaimer
This is an experimental project. Generated code may contain bugs, vulnerabilities, or ethical issues. Always verify outputs before deployment. Features and APIs may change frequently.  