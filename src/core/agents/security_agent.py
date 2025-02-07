# src/core/agents/security_agent.py
from src.utils.config import SecureConfig, ConfigError
from src.core.knowledge_graph import KnowledgeGraph, Node
from typing import Optional, Dict, List
import re
import logging
import json
import os
from zapv2 import ZAPv2  # Import ZAP client
import time
from datetime import datetime
import uuid
from .zap_scan_manager import ZAPScanManager

class SecurityAgent:
    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self.kg = KnowledgeGraph()  # Initialize Knowledge Graph
        self.current_scan_id = None # Track current scan ID
        self.zap_manager = ZAPScanManager()  # Initialize ZAP Scan Manager

        try:
            self._validate_environment()
        except (ValueError, ConfigError) as e:
            self.logger.critical(f"Environment validation failed: {str(e)}")
            raise e

    def _validate_environment(self) -> bool:
        """Validate all security-critical environment variables"""
        try:
            required_vars = ['GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY', 'HUGGING_FACE_API_KEY', 'ZAP_API_KEY']
            for var in required_vars:
                try:
                    value = SecureConfig.get(var)
                    if not value or value == 'invalid' or value.startswith('your_'):
                        raise ValueError(f"Invalid configuration for {var}")
                except ConfigError:
                    # Let ConfigError propagate for missing variables
                    raise
            return True
        except ValueError:
            self.logger.critical(f"Environment validation failed: Invalid configuration")
            raise
        except ConfigError as e:
            self.logger.critical(f"Environment validation failed: Missing required variables")
            raise

    def sanitize_input(self, input_str: str, max_length: int = 1000) -> Optional[str]:
        """Basic input sanitization for API endpoints"""
        if not input_str:
            return None
        sanitized = re.sub(r'[^a-zA-Z0-9\s_\-\.,:;!?]', '', input_str)[:max_length]
        return sanitized.strip()

    def audit_security_event(self, event_type: str, details: dict):
        """Log security events with structured formatting"""
        self.logger.info(f"SECURITY_EVENT|{event_type}|{json.dumps(details)}")

    def run_zap_baseline_scan(self, target_url: str, config_preset: str = "standard") -> Dict:
        """
        Run OWASP ZAP baseline scan with scan manager integration.
        """
        zap_api_key = os.getenv('ZAP_API_KEY', 'changeme')
        zap_address = 'http://zap:8080'

        try:
            zap = ZAPv2(apikey=zap_api_key, proxies={'http': zap_address, 'https': zap_address})
            self.logger.info(f"[SecurityAgent] Starting ZAP baseline scan against: {target_url}")

            # Apply scan configuration preset
            config = self.zap_manager.set_scan_config(config_preset)
            self.logger.info(f"[SecurityAgent] Using scan configuration: {config}")

            # Apply policy and configuration to ZAP
            self._apply_zap_configuration(zap, config)

            # Start scan
            scan_id = zap.ascan.scan(url=target_url, scanpolicyname='Baseline')
            self.current_scan_id = scan_id
            while int(zap.ascan.status(scan_id)) < 100:
                self.logger.info(f"[SecurityAgent] ZAP Scan Progress: {zap.ascan.status(scan_id)}%")
                time.sleep(5)

            self.logger.info(f"[SecurityAgent] ZAP scan completed for: {target_url}")

            # Check for cached results
            cached_results = self.zap_manager.get_cached_results()
            if cached_results:
                self.logger.info("[SecurityAgent] Using cached scan results")
                alerts = cached_results.get("alerts", [])
            else:
                # Fetch fresh results
                alerts = zap.core.alerts()
                self.zap_manager.save_scan_results({"alerts": alerts, "scan_id": scan_id}, target_url)

            self.logger.info(f"[SecurityAgent] Number of ZAP alerts found: {len(alerts)}")
            self._process_zap_results(target_url, alerts)

            # Check for high-risk changes
            if self.zap_manager.has_high_risk_changes({"alerts": alerts}):
                self.audit_security_event("HIGH_RISK_VULNERABILITIES_DETECTED", {
                    "target_url": target_url,
                    "scan_id": scan_id,
                    "alert_count": len([a for a in alerts if a.get("risk") == "High"]) # Corrected to 'High' string
                })

            return {"alerts": alerts, "scan_id": scan_id}

        except Exception as e:
            self.logger.error(f"[SecurityAgent] Error running ZAP scan: {str(e)}")
            return {"error": str(e), "alerts": [], "scan_id": None}

    def _apply_zap_configuration(self, zap: ZAPv2, config: Dict) -> None:
        """
        Apply custom configuration to ZAP scan.
        """
        # Example: Apply attack mode and depth settings
        for setting, value in config.items():
            if setting == "attackMode":
                zap.ascan.set_option_attack_mode(value)
            elif setting == "maxDepth":
                zap.ascan.set_option_max_depth(value)
            elif setting == "maxChildren":
                zap.ascan.set_option_max_children(value)

    def _process_zap_results(self, target_url: str, alerts: List[Dict]): # Modified to accept target_url
        """
        Process ZAP scan findings and store them in the knowledge graph.
        """
        vulnerabilities = [
            alert for alert in alerts
            if alert.get("riskcode", '0') in ['3', '2']  # High (3) and Medium (2) severity as strings
        ]

        for vulnerability in vulnerabilities:
            finding_node = Node(
                type="security_vulnerability",
                content=f"ZAP Finding: {vulnerability.get('name', 'Unknown Vulnerability')}",
                metadata={
                    "target_url": target_url,
                    "vulnerability_name": vulnerability.get("name", "Unknown"),
                    "severity": vulnerability.get("riskcode", '0'), # Keep as string for now
                    "description": vulnerability.get("description", "No description available"), # Corrected key name
                    "solution": vulnerability.get("solution", "No solution available"),
                    "reference": vulnerability.get("reference", "No reference available"),
                    "timestamp": datetime.utcnow().isoformat(),
                    "scan_id": self.current_scan_id
                }
            )
            finding_node_id = self.kg.add_node(finding_node)

            # Create relationships - link vulnerability to target URL as node
            target_node_content = f"Scanned URL: {target_url}"
            target_node_search_results = self.kg.search(target_node_content)
            if target_node_search_results:
                target_node_id = target_node_search_results[0].id
            else:
                target_node = Node(type="scan_target", content=target_node_content, metadata={"url": target_url})
                target_node_id = self.kg.add_node(target_node)

            self.kg.add_edge(finding_node_id, target_node_id, "found_in_scan")


        self.logger.info(f"[SecurityAgent] Processed {len(vulnerabilities)} findings from ZAP scan and stored in KG.")

if __name__ == "__main__":
    import logging
    logging.basicConfig(level=logging.INFO)

    # Example usage (for local testing - ensure docker-compose up -d zap is running)
    agent = SecurityAgent()
    target_to_scan = "http://localhost:5000/generate" # Or your flask app URL
    print(f"Running ZAP scan against: {target_to_scan}")
    scan_results = agent.run_zap_baseline_scan(target_to_scan)
    print(f"ZAP Scan Results: {scan_results}")
