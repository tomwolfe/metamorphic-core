# Metamorphic Software Genesis Ecosystem 🚀

[![CI Status](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml/badge.svg)](https://github.com/tomwolfe/metamorphic-core/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-GPLv3-blue.svg)](LICENSE)

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

The ecosystem is actively under development, with a focus on foundational components:

- **Ethical Validation Framework**: Mechanisms for enforcing and auditing ethical policies
- **Code Analysis Agents**: Tools for static analysis, test generation, and quality assessment
- **LLM Orchestration Layer**: Infrastructure for managing interactions with various LLMs (Currently ~50% done with Phase 1.4)
- **Knowledge Graph**: Repository for ethical principles, analysis data, and system knowledge
- **CI/CD Integration**: Automation for quality assurance processes
- **Security Scanning**: Basic integration with OWASP ZAP for security vulnerability detection

**Note**: While the system is not yet capable of fully autonomous software generation, it currently functions as an advanced AI-powered code analysis and ethical validation framework with basic security scanning capabilities.

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

3. **Start Redis (optional)**:
```bash
docker-compose -f docker-compose.yml.example up -d redis
```

4. **Set Up Virtual Environment**:
```bash
python -m venv venv
source venv/bin/activate  # Linux/macOS
venv\Scripts\activate     # Windows
```

5. **Install Dependencies**:
```bash
pip install --upgrade pip
pip install -r requirements/base.txt
pip install -r requirements/dev.txt
```

### Running the API Server

```bash
cd src/api
python server.py
```

The API server will be available at `http://0.0.0.0:50000/`.

### API Endpoints

Current Functionality:

- `/generate` (GET): Check system status
- `/ethical/analyze` (POST): Analyze code for ethical considerations
- `/ethical/solve-math` (POST): Test mathematical problem-solving
- `/ethical/audit/{state_id}` (GET): Retrieve audit trail data
- `/ethical/visualize/{state_id}` (GET): Obtain visualization data

## Contributing

Contributions are welcome. Please refer to `CONTRIBUTING.md` for guidelines.

## License

This project is licensed under the GNU General Public License v3.0 (GPLv3). See [LICENSE](LICENSE) for details.

## Contact

For inquiries, contact: tomwolfe@gmail.com

**Disclaimer**: This project is in early development and not intended for production use. Functionality is subject to change.
