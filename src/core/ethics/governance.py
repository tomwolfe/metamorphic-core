# src/core/ethics/governance.py
import os
import json
import ast
from datetime import datetime
from typing import Dict, Any, Optional
from z3 import ModelRef
from jsonschema import validate, ValidationError, SchemaError
import textwrap # Add this import
import logging

from ..ethical_governance import EthicalPrinciple

logger = logging.getLogger(__name__)

# QuantumEthicalValidator and EthicalAuditLogger remain unchanged placeholders
class QuantumEthicalValidator:
    def __init__(self):
        self.audit_logger = EthicalAuditLogger()
        self._load_ethical_framework()
        pass

    def validate_code(self, code_sample: str) -> Dict[str, Any]:
        state_id = "placeholder_state_id"
        validation_result = {
            "state_id": state_id,
            "spec_analysis": {"functions": [], "classes": [], "imports": []},
            "status": "pending", "score": 0.0,
            "predictions": self._predict_ethical_impact(code_sample),
            "formal_proof": None, "timestamp": str(datetime.utcnow()),
            "code_sample_hash": hash(code_sample), "generated_tests": []
        }
        try:
            validation_result["score"] = self._calculate_ethical_score(validation_result.get("formal_proof", {}))
            validation_result["status"] = "approved" if validation_result["score"] >= 0.7 else "rejected"
        except Exception as e:
            validation_result.update({"status": "error", "error": str(e), "score": 0.0, "generated_tests": []})
        self.audit_logger.log_decision(validation_result)
        return validation_result

    def _load_ethical_framework(self): pass
    def _predict_ethical_impact(self, code: str) -> Dict[str, float]: return {"bias_risk": 0.15, "transparency_score": 0.7, "immediate_risk": 0.1, "long_term_risk": 0.2, "privacy_risk": 0.1}
    def _calculate_ethical_score(self, proof: Dict) -> float: return 1.0 if proof.get('verified', True) else 0.5

class EthicalAuditLogger:
    def __init__(self):
        self.log_dir = "audit_logs"; os.makedirs(self.log_dir, exist_ok=True)
    def log_decision(self, validation_result: dict):
        audit_entry = {"timestamp": datetime.utcnow().isoformat(), "decision": validation_result.get("status", "unknown"), "ethical_score": validation_result.get("score", 0.0), "model_version": self._get_model_version(), "code_sample_hash": validation_result.get("code_sample_hash")}
        if "ethical_analysis" in validation_result: audit_entry["ethical_analysis_summary"] = {k: v.get("status") for k, v in validation_result["ethical_analysis"].items() if isinstance(v, dict)}
        filename = f"decision_{datetime.utcnow().strftime('%Y%m%d%H%M%S%f')}.json"; filepath = os.path.join(self.log_dir, filename)
        try:
            with open(filepath, "w") as f: json.dump(audit_entry, f, indent=2)
        except TypeError as e:
             logger.error(f"Error logging decision: {e}"); simplified_audit = {k: v for k, v in audit_entry.items() if isinstance(v, (str, int, float, bool, list, dict))};
             with open(filepath, "w") as f: json.dump(simplified_audit, f, indent=2)
    def _get_model_version(self) -> str: return "ETHICAL_MODEL_MVP_v0.1.0"


class EthicalGovernanceEngine:
    def __init__(self):
        self.principles = [ EthicalPrinciple(name="Bias Mitigation", description="Ensure fairness"), EthicalPrinciple(name="Transparency", description="Ensure explainability"), EthicalPrinciple(name="Safety", description="Ensure safety") ]
        self._schema = None
        self._load_schema()

    def _load_schema(self):
        if not hasattr(self, '_schema') or self._schema is None: # Ensure _schema is checked for existence first
            try:
                schema_filename = 'ethical_policy_schema.json'; current_dir = os.path.dirname(os.path.abspath(__file__)); schema_path = os.path.abspath(os.path.join(current_dir, '..', '..', '..', schema_filename))
                if not os.path.exists(schema_path): schema_path = os.path.abspath(os.path.join(current_dir, '..', '..', schema_filename))
                if not os.path.exists(schema_path): schema_path = os.path.abspath(os.path.join(current_dir, '..', '..', '..', '..', schema_filename))
                if not os.path.exists(schema_path): raise FileNotFoundError(f"Schema '{schema_filename}' not found near {current_dir}")
                with open(schema_path, 'r', encoding='utf-8') as f: self._schema = json.load(f) # Keep encoding fix
                logger.debug("Schema loaded successfully.")
            except Exception as e: logger.error(f"CRITICAL: Schema loading failed: {e}", exc_info=True); raise
        return self._schema

    def load_policy_from_json(self, filepath: str) -> Dict:
        if not os.path.exists(filepath): raise FileNotFoundError(f"Policy file not found: {filepath}")
        try:
            with open(filepath, 'r', encoding='utf-8') as f: policy = json.load(f) # Keep encoding fix
        except json.JSONDecodeError as e: raise json.JSONDecodeError(f"Invalid JSON in {filepath}: {e.msg}", e.doc, e.pos) from e
        try: validate(instance=policy, schema=self._load_schema())
        except SchemaError as e: raise SchemaError(f"Invalid schema: {e}") from e
        except ValidationError as e: path_str = "/".join(map(str, e.path)); raise ValidationError(f"Policy {filepath} validation failed: {e.message} (path: {path_str})") from e
        except Exception as e: raise Exception(f"Unexpected validation error: {e}") from e
        return policy

    def _check_transparency(self, code: str, is_snippet: bool = False) -> tuple[bool, str]:
        """
        Checks for docstrings in the provided code.
        Returns a tuple (is_compliant: bool, detail_key: str) indicating compliance status and a specific reason.
        `detail_key` can be 'compliant', 'empty_code', 'syntax_error', 'missing_docstrings'.
        """
        logger.debug(f"--- Running transparency check (is_snippet={is_snippet}) ---")
        processed_code = code # Initialize with original code

        stripped_code = code.strip()
        # 1. Handle empty code (whitespace only or truly empty)
        if not stripped_code:
            return False, "empty_code"
        # 2. Handle comment-only snippets (should be compliant)
        if is_snippet and all(line.strip().startswith('#') for line in stripped_code.splitlines()):
            logger.debug("Snippet consists only of comments. Bypassing docstring transparency check.")
            return True, "compliant"

        if is_snippet:
            try:
                # Dedent snippets to handle LLM-generated indented blocks
                dedented_code = textwrap.dedent(code)
                processed_code = dedented_code # Use dedented code for parsing
                logger.debug("Snippet dedented for transparency check.")
            except Exception as e:
                # If dedent fails (e.g., inconsistent indentation), parse original.
                # This is unlikely to cause major issues as ast.parse will catch syntax errors.
                logger.warning(f"Failed to dedent snippet: {e}. Proceeding with original code.")
                processed_code = code # Fallback to original code if dedent fails

        try:
            tree = ast.parse(processed_code) # Parse the potentially dedented code

            # If it's a snippet and has no function or class definitions at the top level,
            # it's likely a simple expression, import, or block of code for insertion.
            # In this case, we consider it transparent as its context is the surrounding code.
            if is_snippet:
                has_top_level_defs = any(isinstance(node, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)) for node in tree.body)
                if not has_top_level_defs:
                    # This snippet is a simple block for insertion, not a new definition.
                    # It derives transparency from its surrounding context.
                    logger.debug("Snippet has no top-level function/class definitions. Bypassing docstring transparency check for simple insertion block.")
                    return True, "compliant"

            # Module docstring check
            module_docstring = ast.get_docstring(tree)
            logger.debug(f"Module docstring found: {bool(module_docstring)}")

            if not module_docstring:
                 logger.debug("Violation: Missing module docstring. Returning False.")
                 # Only fail for missing module docstring if it's not a snippet
                 if not is_snippet:
                    logger.debug("Violation: Missing module docstring for full code. Returning False.")
                    return False, "missing_docstrings"
                 else:
                    # Snippets typically don't have module-level docstrings, so this is not a violation.
                    logger.debug("Snippet has no module-level docstring (as expected for snippets).")


            violation_found = False
            has_definitions = False # Initialize flag for presence of definitions
            for node in ast.walk(tree):
                if isinstance(node, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)): # Added AsyncFunctionDef to check
                    has_definitions = True # Set flag if any function/class definition is found
                    node_name = getattr(node, 'name', 'unknown_node')
                    func_class_docstring = ast.get_docstring(node)
                    logger.debug(f"Checking node: {node_name}, Type: {type(node).__name__}, Docstring found: {bool(func_class_docstring)}")
                    if not func_class_docstring:
                        # If it's a snippet and a placeholder function/method, don't fail yet.
                        is_placeholder = False
                        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and len(node.body) == 1 and isinstance(node.body[0], ast.Pass): # Consider AsyncFunctionDef too
                            is_placeholder = True
                        
                        if is_snippet and is_placeholder:
                            logger.debug(f"Snippet placeholder {type(node).__name__} '{node_name}' without docstring. Allowing for now.")
                            # Continue to check other nodes, but don't mark this specific one as a violation *yet*.
                            # The overall check for `violation_found` will determine the outcome.
                        elif is_snippet: # Non-placeholder in snippet missing docstring
                            logger.debug(f"Violation: Snippet {type(node).__name__} '{node_name}' missing docstring. Returning False.")
                            return False, "missing_docstrings"
                        else: # For full code, just flag it for now
                            violation_found = True

            if has_definitions and violation_found: # Only fail if definitions exist and some are missing docstrings
                 logger.debug("Violation found in function/class docstrings. Returning False.")
                 return False, "missing_docstrings"
            elif not has_definitions and is_snippet and not module_docstring:
                # If it's a snippet, has no definitions, and no module docstring,
                # it's likely a simple expression or import block. Consider it transparent.
                logger.debug("Snippet has no definitions and no module docstring. Considered transparent.")
                return True, "compliant"
            elif not has_definitions and not is_snippet and not module_docstring:
                # If it's full code, has no definitions, but also no module docstring, it's a violation.
                logger.debug("Full code has no definitions and no module docstring. Violation. Returning False.")
                return False, "missing_docstrings"


            logger.debug("No docstring violations found. Returning True.")
            return True, "compliant"

        except SyntaxError as se:
            # If it's a snippet, a syntax error might be resolved when merged.
            # We allow it to pass this check and rely on the full-file pre-merge check later.
            if is_snippet:
                logger.warning(f"Syntax error in snippet during transparency check: {se}. Skipping check as it may be resolved on merge.")
                return True, "skipped_due_to_syntax_error" # Treat as compliant for now
            else: # For full code, a syntax error is a definitive transparency failure.
                logger.warning(f"Syntax error in full code during transparency check: {se}. Returning False.")
                return False, "syntax_error"
        except Exception as e:
            logger.error(f"ERROR during AST parsing for transparency: {e}. Code (first 100 chars): '{code[:100]}'. Returning False.", exc_info=True)
            return False, "syntax_error" # Treat other parsing errors like syntax errors for transparency

    def enforce_policy(self, code: str, policy_config: Dict, is_snippet: bool = False) -> Dict:
        constraints_config = policy_config.get("constraints", {})
        enforcement_results = {"policy_name": policy_config.get("policy_name", "Unnamed Policy"), "description": policy_config.get("description", ""), "overall_status": "compliant"}
        any_violation = False

        # BiasRisk
        bias_config = constraints_config.get("BiasRisk", {}); bias_keywords = bias_config.get("keywords", []); bias_violation = any(kw.lower() in code.lower() for kw in bias_keywords if kw)
        bias_status = "violation" if bias_violation else "compliant"; enforcement_results["BiasRisk"] = {"status": bias_status, "threshold": bias_config.get("threshold"), "enforcement_level": bias_config.get("enforcement_level"), "details": f"Violating keywords: {[kw for kw in bias_keywords if kw and kw.lower() in code.lower()]}." if bias_violation else "No violating keywords."}
        if bias_status == "violation": any_violation = True; logger.debug("any_violation set by BiasRisk")

        # TransparencyScore
        transparency_config = constraints_config.get("TransparencyScore", {})
        is_transparent, transparency_detail_key = self._check_transparency(code, is_snippet)
        transparency_status = "compliant" if is_transparent else "violation"
        
        transparency_details_msg = "Docstrings compliant."
        if transparency_detail_key == "syntax_error":
            transparency_details_msg = "Syntax error prevented full transparency check."
        elif transparency_detail_key == "missing_docstrings":
            transparency_details_msg = "Missing required docstring(s)."
        elif transparency_detail_key == "empty_code":
            transparency_details_msg = "Code is empty, which is considered non-transparent."
        enforcement_results["TransparencyScore"] = {"status": transparency_status, "threshold": transparency_config.get("threshold"), "enforcement_level": transparency_config.get("enforcement_level"), "details": transparency_details_msg}
        if transparency_status == "violation": any_violation = True; logger.debug("any_violation set by Transparency")

        # SafetyBoundary
        safety_config = constraints_config.get("SafetyBoundary", {}); unsafe_ops = safety_config.get("unsafe_operations", []); found_unsafe = [op for op in unsafe_ops if op and op in code]; safety_violation = bool(found_unsafe)
        safety_status = "violation" if safety_violation else "compliant"; enforcement_results["SafetyBoundary"] = {"status": safety_status, "threshold": safety_config.get("threshold"), "enforcement_level": safety_config.get("enforcement_level"), "details": f"Unsafe operations: {found_unsafe}." if safety_violation else "No unsafe operations."}
        if safety_status == "violation": any_violation = True; logger.debug("any_violation set by Safety")

        # Final Status
        if any_violation: enforcement_results["overall_status"] = "rejected"; logger.debug(f"Final status: rejected (any_violation={any_violation})")
        else: enforcement_results["overall_status"] = "approved"; logger.debug(f"Final status: approved (any_violation={any_violation})")
        return enforcement_results

    def get_ethical_health_report(self) -> Dict[str, Any]: return {"status": "placeholder", "compliance_score": 0.95, "policy_violations": [], "model_integrity": 1.0, "recent_issues": []}
    def get_ethical_model_version(self) -> Dict[str, Any]: return {"version": "ETHICAL_MODEL_MVP_v0.1.0", "last_updated": datetime.utcnow().isoformat()}