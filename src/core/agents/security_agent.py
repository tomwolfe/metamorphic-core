# src/core/agents/security_agent.py
from src.utils.config import SecureConfig, ConfigError
from src.core.knowledge_graph import KnowledgeGraph
from typing import Optional, Dict, List
import re
import logging
import json
import os
from zapv2 import ZAPv2  # Import ZAP client
import time

class SecurityAgent:
    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self.kg = KnowledgeGraph()  # Initialize Knowledge Graph
        try:
            self._validate_environment()
        except (ValueError, ConfigError) as e:
            self.logger.critical(f"Environment validation failed: {str(e)}")
            raise e

    def _validate_environment(self) -> bool:
        """Validate all security-critical environment variables"""
        try:
            required_vars = ['GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY', 'HUGGING_FACE_API_KEY']
            for var in required_vars:
                if var not in os.environ:
                    raise ConfigError(f"Missing required environment variable: {var}")
                value = os.environ[var]
                if not value or value == 'invalid' or value.startswith('your_'):
                    raise ValueError(f"Invalid configuration for {var}")
            return True
        except (ValueError, ConfigError) as e:
            self.logger.critical(f"Environment validation failed: {str(e)}")
            raise e

    def sanitize_input(self, input_str: str, max_length: int = 1000) -> Optional[str]:
        """Basic input sanitization for API endpoints"""
        if not input_str:
            return None
        sanitized = re.sub(r'[^a-zA-Z0-9\s_\-\.,:;!?]', '', input_str)[:max_length]
        return sanitized.strip()

    def audit_security_event(self, event_type: str, details: dict):
        """Log security events with structured formatting"""
        self.logger.info(f"SECURITY_EVENT|{event_type}|{json.dumps(details)}")

    def run_zap_baseline_scan(self, target_url: str): # Modified to take target_url
        """
        Run OWASP ZAP baseline scan and process findings.
        """
        zap_api_key = os.getenv('ZAP_API_KEY', 'changeme') # default API key from docker-compose
        zap_address = 'http://localhost:8080' if os.getenv('CI') else 'http://zap:8080'

        try:
            zap = ZAPv2(apikey=zap_api_key, proxies={'http': zap_address, 'https': zap_address})
            self.logger.info(f"[SecurityAgent] Starting ZAP baseline scan against: {target_url}")

            # Actively scan the target
            scan_id = zap.ascan.scan(target_url=target_url, scanpolicyname='Baseline')
            while int(zap.ascan.status(scan_id)) < 100:
                self.logger.info(f"[SecurityAgent] ZAP Scan Progress: {zap.ascan.status(scan_id)}%")
                time.sleep(5)

            self.logger.info(f"[SecurityAgent] ZAP scan completed for: {target_url}")
            # Fetch alerts
            alerts = zap.core.alerts()
            self.logger.info(f"[SecurityAgent] Number of ZAP alerts found: {len(alerts)}")
            self._process_zap_results(target_url, alerts) # Pass target_url to processing
            return alerts # Return alerts for testing/debugging

        except Exception as e:
            self.logger.error(f"[SecurityAgent] Error running ZAP scan: {str(e)}")
            return {"error": str(e), "alerts": []}

    def _process_zap_results(self, target_url: str, alerts: List[Dict]): # Modified to accept target_url
        """
        Process ZAP scan findings and store them in the knowledge graph.
        """
        vulnerabilities = [
            alert for alert in alerts
            if alert.get("riskcode", '0') in ['3', '2']  # High (3) and Medium (2) severity as strings
        ]

        for vulnerability in vulnerabilities:
            self.kg.add_security_finding(
                target_url=target_url,
                vulnerability_name=vulnerability.get("name", "Unknown"),
                severity=vulnerability.get("riskcode", '0'), # Keep as string for now
                description=vulnerability.get("description", "No description available"), # Corrected key name
                solution=vulnerability.get("solution", "No solution available"),
                reference=vulnerability.get("reference", "No reference available")
            )

        self.logger.info(f"[SecurityAgent] Processed {len(vulnerabilities)} findings from ZAP scan.")

if __name__ == "__main__":
    import logging
    logging.basicConfig(level=logging.INFO)

    # Example usage (for local testing - ensure docker-compose up -d zap is running)
    agent = SecurityAgent()
    target_to_scan = "http://localhost:5000/generate" # Or your flask app URL
    print(f"Running ZAP scan against: {target_to_scan}")
    scan_results = agent.run_zap_baseline_scan(target_to_scan)
    print(f"ZAP Scan Results: {scan_results}")
