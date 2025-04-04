# INSTALL.md

## Production Installation

For production deployments, it is recommended to use a virtual environment and install only the base requirements:

```bash
# Create a virtual environment (if you don't have one already)
python -m venv venv-prod
source venv-prod/bin/activate  # On Linux/macOS
# venv-prod\Scripts\activate  # On Windows

# Install only production dependencies
pip install -r requirements/base.txt
```

## Development Installation

For development and testing, install both base and development requirements within a virtual environment.

**Detailed Development Setup Steps:**

1.  **Verify Python 3.11+ is Installed:**
    *   Open your terminal and run: `python --version`
    *   **Ensure the output shows Python 3.11 or higher.** If not, download and install Python 3.11+ from [python.org](https://www.python.org/downloads/).
2.  **Create a Virtual Environment:**
    ```bash
    python -m venv venv-dev  # Create a virtual environment named 'venv-dev'
    ```
3.  **Activate the Virtual Environment:**
    *   **On Linux/macOS:**
        ```bash
        source venv-dev/bin/activate
        ```
    *   **On Windows:**
        ```bash
        venv-dev\Scripts\activate
        ```
    *   **(Important): Ensure your terminal prompt now shows `(venv-dev)` indicating the virtual environment is active.**
4.  **Install Python Dependencies:**
    ```bash
    pip install --upgrade pip  # Upgrade pip to the latest version (recommended)
    pip install -r requirements/base.txt  # Install base dependencies
    pip install -r requirements/dev.txt   # Install development dependencies (includes testing tools, linters etc.)
    ```
5.  **Install Pre-commit Hooks (Optional, but Recommended for Development):**
    ```bash
    pip install pre-commit  # Install pre-commit
    pre-commit install     # Set up pre-commit hooks in your local Git repository
    ```
    *   Pre-commit hooks will automatically run code checks (like formatting and linting) before each commit.

**Troubleshooting Installation Issues:**

*   **Python Version Issues:**
    *   If `python --version` shows an older version, ensure Python 3.11+ is correctly installed and is the default Python version used by your terminal. You might need to use `python3.11` or `py -3.11` depending on your system.
    *   Virtual environments isolate your project's Python version. Ensure you activate the virtual environment (`venv-dev`) for your project.

*   **`pip install` Errors:**
    *   **Permission Errors:** If you encounter permission errors during `pip install`, you might need to use the `--user` flag (though virtual environments are recommended to avoid this).
    *   **Dependency Conflicts:** If you encounter dependency conflicts, try upgrading `pip` (`pip install --upgrade pip`) and ensure your `venv-dev` virtual environment is clean (try creating a new virtual environment).
    *   **Network Issues:** Check your internet connection if `pip install` fails to download packages.

*   **Pre-commit Installation Errors:**
    *   Ensure `pre-commit` is installed (`pip install pre-commit`) before running `pre-commit install`.
    *   Check the pre-commit documentation for troubleshooting common issues: [pre-commit documentation](https://pre-commit.com/#installation).

If you continue to experience installation problems, please consult the project's `README.md` for further troubleshooting tips or create a new issue in the project's GitHub repository with details about your operating system, Python version, and the error messages you are encountering.
