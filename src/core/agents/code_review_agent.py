# src/core/agents/code_review_agent.py
# File: src/core/agents/code_review_agent.py
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
    def __init__(self, kg: KnowledgeGraph=None): # Added default None for kg for easier instantiation in some contexts
        self.kg = kg if kg is not None else KnowledgeGraph() # Initialize KG if not provided
        self.issue_pattern = re.compile(
            r"(?P<file>.+):(?P<line>\d+):(?P<col>\d+): (?P<code>\w+) (?P<msg>.+)")

    def analyze_python(self, code: str) -> dict:
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=True) as tmp:
                os.chmod(tmp.name, 0o600) # Restrict file permissions
                tmp.write(code)
                tmp.flush()
                result = subprocess.run(
                    ['flake8', tmp.name],
                    capture_output=True,
                    text=True,
                    check=True
                )
                flake8_results = self._parse_flake8_results(result.stdout)

                bandit_results = self._run_bandit(code)

                merged_results = self._merge_results(flake8_results, bandit_results)
                if bandit_results['error']: # If bandit had an error, report it in merged results
                    merged_results['error'] = True
                    merged_results['error_message'] = merged_results.get('error_message', '') +  " Bandit: " + bandit_results['error_message']

                if not merged_results.get('error') and merged_results['static_analysis']:
                    code_hash = hash(code)
                    self.store_findings(merged_results, str(code_hash), code) # Pass code to store_findings

                return merged_results

        except json.JSONDecodeError as e: # Bandit can return malformed JSON
            logger.error(f"JSONDecodeError from bandit: {e}")
        except subprocess.CalledProcessError as e:
            logger.error(f"Flake8 analysis failed with return code: {e.returncode}")
            logger.error(f"Flake8 stderr: {e.stderr}")
            return {
                'error': True,
                'error_message': f"Flake8 analysis failed: {e}",
                'static_analysis': []
            }
        except FileNotFoundError as e:
            logger.error(f"Flake8 executable not found: {str(e)}")
            return {
                'error': True,
                'error_message': f"Flake8 executable not found: {str(e)}",
                'static_analysis': []
            }
        except Exception as e:
            logger.error(f"Error running flake8: {str(e)}")
            return {
                'error': True,
                'error_message': f"Error running flake8: {str(e)}",
                'static_analysis': []
            }

    def _run_bandit(self, code: str) -> dict:
        """
        Runs Bandit security linter and returns findings.
        """
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=True) as tmp:
                os.chmod(tmp.name, 0o600) # Restrict file permissions
                tmp.write(code)
                tmp.flush()
                result = subprocess.run(
                    ['bandit', '-f', 'json', '-q', tmp.name], # -q for quiet output
                    capture_output=True,
                    text=True,
                    check=True
                )
                if result.stdout: # Check if stdout is not empty before parsing
                    return {
                        'findings': json.loads(result.stdout)['results'] if result.stdout else [],
                        'error': False,
                        'error_message': None
                    }
                else:
                    return {'findings': [], 'error': False, 'error_message': None} # Return empty list if no output from bandit

        except FileNotFoundError as e:
            logger.error(f"Bandit executable not found: {str(e)}")
            return {'findings': [], 'error': True, 'error_message': f"Bandit executable not found: {str(e)}"}
        except subprocess.CalledProcessError as e:
            logger.error(f"Bandit analysis failed with return code: {e.returncode}")
            logger.error(f"Bandit stderr: {e.stderr}")
            return {'findings': [], 'error': True, 'error_message': f"Bandit analysis failed: {e}"}
        except json.JSONDecodeError as e:
            logger.error(f"JSONDecodeError parsing Bandit output: {e}")
            logger.error(f"Bandit Output (non-JSON): {result.stdout}") # Log raw output
            return {'findings': [], 'error': True, 'error_message': f"Error parsing Bandit JSON output: {e}"}
        except Exception as e:
            logger.error(f"Error running bandit: {str(e)}")
            return {'findings': [], 'error': True, 'error_message': f"Error running bandit: {str(e)}"}


    def _merge_results(self, flake8_results: dict, bandit_results: dict) -> dict:
        """
        Merges results from Flake8 and Bandit, standardizing the format.
        """
        static_analysis_findings = flake8_results.get('static_analysis', [])

        merged = {
            'static_analysis': static_analysis_findings,
            'errors': []
        }
        if not bandit_results['error']: # Process bandit findings only if no error
            for bandit_finding in bandit_results['findings']:
                merged['static_analysis'].append({
                    'file': bandit_finding.get('filename'),
                    'line': str(bandit_finding.get('line_number')), # Convert to string to match flake8
                    'col': '0', # Bandit does not provide column
                    'code': bandit_finding.get('test_id'),
                    'msg': bandit_finding.get('issue_text', 'No message provided'),
                    'severity': self._map_bandit_severity(bandit_finding.get('issue_severity', 'LOW').upper())
                })
        return merged

    def store_findings(self, findings: dict, code_hash: str, code: str): # Added code parameter
        """Store static analysis findings in the Knowledge Graph."""
        node = Node(
            type="code_review",
            content="Static analysis findings from flake8 with severity", # Updated content for clarity
            metadata={
                "code_hash": code_hash,
                "code_snippet": self._get_code_snippet(code), # Store full code snippet - changed to full snippet
                "findings": [{**f, 'severity': f.get('severity', 'unknown')} for f in findings['static_analysis']], # Add severity to each finding
                "timestamp": datetime.utcnow().isoformat()
            }
        )
        self.kg.add_node(node)

    def _get_code_snippet(self, code: str, line_num: int = None, context: int = 5) -> str:
        """Extracts a code snippet around a given line number.
           If line_num is None, returns the whole code."""
        if line_num is None:
            return code.strip() # Return full code if line_num not specified

        lines = code.split('\n')
        if not lines:
            return ''  # Handle empty code
        start = max(0, line_num - context - 1)
        end = min(len(lines), line_num + context)
        # Adjust line numbers for display (1-based indexing)
        return "\n".join(f"{i+1:4d} | {line}" for i, line in enumerate(lines[start:end], start=start))

    def _parse_flake8_results(self, output: str) -> dict: # Removed code parameter
        findings = []
        severity_map = {
            'E': 'error',          # General Errors
            'F': 'error',          # Fatal errors
            'W': 'warning',        # Warnings
            'C': 'warning',        # Conventions (potential issues)
            'E001': 'style',       # Flake8 E001: Whitespace error
            'E002': 'style',       # Flake8 E002: Continuation line indentation
            'E123': 'style',       # Flake8 E123: Indentation not a multiple of four
            'E1': 'style', 'W6': 'style',  # PEP8 style (example subsets)
            'E2': 'style', 'E3': 'style', 'E4': 'style', 'E5': 'style',
            'E7': 'style', 'E9': 'style', 'C0': 'style', 'C4': 'style', 'C9': 'style', # More PEP8
            'B': 'warning',        # Bug Bear
            'D': 'info',           # Documentation (pydocstyle)
            'N': 'info',           # Naming conventions
            'T': 'info',           # Type hint checks
            'S': 'security',       # Bandit security issues
            'PL': 'style',         # Pylint (if integrated) - example for future plugins
            'B9': 'security'       # Flake8-bugbear security - example
        }

        for match in self.issue_pattern.finditer(output):
            issue_details = match.groupdict()
            code = issue_details['code']  # Use full code for specific mapping
            issue_details['severity'] = severity_map.get(code, severity_map.get(code[0], 'info')) # Assign severity from map
            #issue_details['code_snippet'] = self._get_code_snippet(code, int(issue_details['line'])) # Get snippet for each issue # Removed to store whole snippet in node metadata
            findings.append(issue_details)
        return {'static_analysis': findings}

    def _map_bandit_severity(self, bandit_severity: str) -> str:
        """Maps Bandit severity levels to our standard severity levels."""
        if bandit_severity in ['HIGH', 'MEDIUM']:
            return 'security_high' # More specific security severity
        elif bandit_severity == 'LOW':
            return 'security_low' # Differentiate low security risks
        else:
            return 'info' # Default for unknown
