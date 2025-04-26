# src/core/agents/code_review_agent.py
# src/core/agents/code_review_agent.py
from src.core.knowledge_graph import KnowledgeGraph, Node
import subprocess
import tempfile
import re
import json
import logging
import os
from datetime import datetime

logger = logging.getLogger(__name__)

class CodeReviewAgent:
    def __init__(self, kg: KnowledgeGraph=None):
        self.kg = kg if kg is not None else KnowledgeGraph()
        # Corrected regex from LLM Solution 2
        self.issue_pattern = re.compile(
            r"^(?P<file>.+):(?P<line>\d+):(?P<col>\d+): (?P<code>\w+) (?P<message>.+)$"
        )

    def analyze_python(self, code: str) -> dict:
        """Analyze Python code using Flake8 and Bandit."""
        flake8_results = {'static_analysis': [], 'output': ''}
        bandit_results = {'findings': [], 'error': False, 'error_message': None}  # Initialize bandit_results

        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=True) as tmp:
                os.chmod(tmp.name, 0o600)
                tmp.write(code)
                tmp.flush()
                tmp_name = tmp.name # Keep the temporary file name after flush

                # --- Flake8 Analysis ---
                try:
                    result_flake8 = subprocess.run(
                        ['flake8', tmp_name], # Use tmp_name
                        capture_output=True,
                        text=True,
                        check=False
                    )
                    flake8_output = result_flake8.stdout.strip()
                    flake8_results['output'] = flake8_output
                    flake8_results['static_analysis'] = self._parse_flake8_results(flake8_output)

                    logger.debug(f"Flake8 raw stdout: {result_flake8.stdout}")
                    logger.debug(f"Flake8 raw stderr: {result_flake8.stderr}")

                except FileNotFoundError as e:
                    logger.error(f"Flake8 executable not found: {str(e)}")
                    flake8_results['error'] = True
                    flake8_results['error_message'] = f"FileNotFoundError: {str(e)}"
                except Exception as e:
                    logger.error(f"Error running flake8: {str(e)}", exc_info=True)
                    flake8_results['error'] = True
                    flake8_results['error_message'] = f"Error running flake8: {str(e)}"

                # --- Bandit Analysis ---
                try:
                    result_bandit = subprocess.run(
                        ['bandit', '-r', tmp_name, '-f', 'json'], # Use tmp_name
                        capture_output=True,
                        text=True,
                        check=False
                    )
                    bandit_output = result_bandit.stdout.strip()

                    logger.debug(f"Bandit raw stdout: {result_bandit.stdout}")
                    logger.debug(f"Bandit raw stderr: {result_bandit.stderr}")

                    if result_bandit.returncode != 0 and not bandit_output:
                         # Bandit might return non-zero on some issues, but should still produce JSON.
                         # If returncode is non-zero AND output is empty, it's likely an execution error.
                         logger.error(f"Bandit execution failed with return code {result_bandit.returncode} and no output. Stderr:\n{result_bandit.stderr}")
                         bandit_results['error'] = True
                         bandit_results['error_message'] = f"Bandit execution failed (return code {result_bandit.returncode}). Stderr: {result_bandit.stderr}"
                    elif bandit_output:
                        try:
                            bandit_json = json.loads(bandit_output)
                            # FIX: Call _parse_bandit_results to map keys and severity
                            bandit_results['findings'] = self._parse_bandit_results(bandit_json)
                        except json.JSONDecodeError as e:
                            logger.error(f"Error parsing Bandit JSON output: {e}. Raw output:\n{bandit_output}", exc_info=True)
                            bandit_results['error'] = True
                            bandit_results['error_message'] = f"Error parsing Bandit JSON output: {e}"
                            bandit_results['raw_output'] = bandit_output # Include raw output for debugging
                    else:
                         # Bandit ran, returned 0, but had no output (e.g., no findings)
                         logger.info("Bandit ran successfully with no findings.")


                except FileNotFoundError as e:
                    logger.error(f"Bandit executable not found: {str(e)}")
                    bandit_results['error'] = True
                    bandit_results['error_message'] = f"Bandit executable not found: {str(e)}"
                except Exception as e:
                    logger.error(f"Error running bandit: {str(e)}", exc_info=True)
                    bandit_results['error'] = True
                    bandit_results['error_message'] = f"Error running bandit: {str(e)}"

        except Exception as e:
            logger.error(f"Unexpected error during temporary file handling: {str(e)}", exc_info=True)
            return {'error': f"Unexpected file handling error: {str(e)}", 'static_analysis': []}

        # --- Merge Results ---
        # Merge Flake8 and Bandit findings
        merged_findings = self._merge_results(flake8_results, bandit_results)

        # Determine overall status based on findings and errors
        overall_status = "success"
        if flake8_results.get('error') or bandit_results.get('error'):
            overall_status = "error"
        # Check for findings with severity 'error' (from Flake8 E/F) or 'security_high' (from Bandit HIGH)
        elif any(f.get('severity', '').startswith('error') or f.get('severity', '').startswith('security_high') for f in merged_findings.get('static_analysis', [])):
             overall_status = "failed" # Consider errors or high security issues as failure

        return {
            'status': overall_status,
            'flake8_output': flake8_results.get('output', ''),
            'static_analysis': merged_findings.get('static_analysis', []),
            'errors': {
                'flake8': flake8_results.get('error_message'),
                'bandit': bandit_results.get('error_message')
            }
        }


    def _parse_flake8_results(self, output: str) -> list: # Return type is list of findings
        """Parse Flake8 output into structured findings."""
        findings = []
        for line in output.splitlines():
            match = self.issue_pattern.match(line)
            if match:
                details = match.groupdict()
                details["severity"] = self._determine_severity(details["code"])
                # CORRECTED: Ensure 'message' key is used consistently
                details['message'] = details.pop('message') # Rename 'message' group to 'message' key
                findings.append(details)
        return findings

    def _determine_severity(self, code: str) -> str:
        """Map Flake8 error codes to severity levels."""
        severity_map = {
            'E': 'error',
            'F': 'error',
            'W': 'warning',
            'C': 'warning',
            'S': 'security', # Although 'S' is not flake8 standard, kept for potential extensions
            'B9': 'security', # Although 'B9' is not flake8 standard, kept for potential extensions
            'PL': 'style',     # Pylint - example for future plugins
            'D': 'info',      # Documentation (pydocstyle)
            'N': 'info',      # Naming conventions
            'T': 'info'       # Type hints
        }
        # Default to 'info' if code prefix is not in map
        return severity_map.get(code[0], 'info') if code and len(code) > 0 else 'info' # Added check for empty code string

    def _parse_bandit_results(self, bandit_json: dict) -> list:
        """Parse Bandit JSON output into structured findings."""
        findings = []
        for issue in bandit_json.get('results', []):
            findings.append({
                'file': issue.get('filename', 'N/A'),
                'line': str(issue.get('line_number', 'N/A')),
                'col': 'N/A', # Bandit doesn't provide column
                'code': issue.get('test_id', 'N/A'), # Map test_id to 'code'
                'message': issue.get('issue_text', 'N/A'), # Map issue_text to 'message'
                'severity': self._map_bandit_severity(issue.get('issue_severity', 'UNKNOWN')),
                'confidence': issue.get('issue_confidence', 'UNKNOWN')
            })
        return findings

    def _map_bandit_severity(self, severity: str) -> str:
        """Map Bandit severity strings to internal severity levels."""
        severity_map = {
            'HIGH': 'security_high',
            'MEDIUM': 'security_medium',
            'LOW': 'security_low',
            'INFO': 'info'
        }
        return severity_map.get(severity.upper(), 'info')

    def _merge_results(self, flake8_results: dict, bandit_results: dict) -> dict:
        """Merge parsed results from Flake8 and Bandit."""
        # flake8_results['static_analysis'] contains findings parsed by _parse_flake8_results
        # bandit_results['findings'] contains findings parsed by _parse_bandit_results
        merged_static_analysis = flake8_results.get('static_analysis', []) + bandit_results.get('findings', [])
        return {'static_analysis': merged_static_analysis}