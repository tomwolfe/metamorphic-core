# src/core/agents/security_agent/zap_scan_manager.py
from typing import Dict, List, Optional
from datetime import datetime
import json
import pickle
import os

class ZAPScanManager:
    """
    Manages ZAP scan configurations, results, and policies.
    Implements caching, configuration presets, and scan history tracking.
    """
    
    def __init__(self):
        self.config_presets = {
            "strict": {"attackMode": 1, "maxDepth": 5, "maxChildren": 100},
            "standard": {"attackMode": 0, "maxDepth": 3, "maxChildren": 50},
            "basic": {"attackMode": 0, "maxDepth": 1, "maxChildren": 25}
        }
        
        self._scan_history: List[Dict] = []
        self._baseline_policy: Optional[Dict] = None
        self._cache_location = "zap_scan_cache.pkl"
        
        # Load existing baseline policy if available
        self._load_baseline_policy()
        
    def set_scan_config(self, preset_name: str) -> Dict:
        """
        Applies scan configuration preset.
        """
        if preset_name not in self.config_presets:
            raise ValueError("Invalid preset name")
            
        config = self.config_presets[preset_name].copy()
        if self._baseline_policy:
            config.update(self._baseline_policy)
            
        return config
        
    def _load_baseline_policy(self):
        """
        Loads baseline policy from disk.
        """
        policy_file = "zap_baseline_policy.json"
        if os.path.exists(policy_file):
            with open(policy_file, 'r') as f:
                self._baseline_policy = json.load(f)
                
    def save_scan_results(self, results: Dict, target_url: str):
        """
        Caches scan results and updates scan history.
        """
        timestamp = datetime.utcnow().isoformat()
        
        # Cache results
        with open(self._cache_location, 'wb') as f:
            pickle.dump(results, f)
            
        # Update history
        self._scan_history.append({
            "timestamp": timestamp,
            "target": target_url,
            "alerts": len(results.get("alerts", [])),
            "high_risk": sum(1 for a in results.get("alerts", []) 
                            if a.get("risk") == "high"),
            "medium_risk": sum(1 for a in results.get("alerts", []) 
                             if a.get("risk") == "medium")
        })
        
    def get_scan_history(self) -> List[Dict]:
        """
        Returns scan history with key metrics.
        """
        return self._scan_history
    
    def has_high_risk_changes(self, new_results: Dict) -> bool:
        """
        Checks for high-risk changes since last scan.
        """
        if not self._scan_history:
            return False
            
        last_high_risk = self._scan_history[-1]["high_risk"]
        new_high_risk = sum(1 for a in new_results.get("alerts", [])
                           if a.get("risk") == "high")
                           
        return new_high_risk > last_high_risk
    
    def get_cached_results(self) -> Optional[Dict]:
        """
        Returns cached scan results if available.
        """
        if os.path.exists(self._cache_location):
            with open(self._cache_location, 'rb') as f:
                return pickle.load(f)
        return None
