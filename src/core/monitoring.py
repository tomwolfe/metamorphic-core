# src/core/monitoring.py
import time
from collections import defaultdict
from typing import Dict, Any
import os # Import os for environment variable check

class TelemetryData:
    def __init__(self):
        self.token_usage = defaultdict(int)
        self.model_usage = defaultdict(int)
        self.ethical_checks = 0
        self.operation_latency = defaultdict(float)
        self.constraint_violations = defaultdict(int)

    def to_dict(self) -> Dict[str, Any]:
        return {
            'token_usage': self.token_usage,
            'model_usage': self.model_usage,
            'ethical_checks': self.ethical_checks,
            'operation_latency': self.operation_latency,
            'constraint_violations': self.constraint_violations,
        }

class Telemetry:
    def __init__(self):
        self.data = TelemetryData()
        self._session_start_time = None

    def start_session(self):
        self.data = TelemetryData() # Reset data on new session
        self._session_start_time = time.time()

    def end_session(self):
        if self._session_start_time:
            self.data.operation_latency['generate'] = time.time() - self._session_start_time
        self._session_start_time = None

    def track(self, event_type: str, tags: dict = None, metrics: dict = None):
        if tags is None:
            tags = {}
        if metrics is None:
            metrics = {}

        if event_type == 'token_usage':
            for model, tokens in metrics.items():
                self.data.token_usage[model] += tokens
        elif event_type == 'model_usage':
            model_name = tags.get('model')
            if model_name:
                self.data.model_usage[model_name] += 1
        elif event_type == 'ethical_check':
            self.data.ethical_checks += 1
        elif event_type == 'constraint_violation':
            constraint_type = tags.get('constraint')
            if constraint_type:
                self.data.constraint_violations[constraint_type] += 1
        elif event_type == 'verification_failure':
            pass # Or log specific verification failure details if needed
        elif event_type == 'error':
            pass # Generic error tracking, details in tags if needed
        elif event_type == 'model_fallback':
            pass # Track model fallback events
        elif event_type == 'model_success':
            pass # Track model success events


    def span(self, operation_name: str):
        return OperationSpan(self, operation_name)

    def publish(self):
        self.end_session()
        report = self.generate_report()
        print(report) # Simple print for now, can be replaced with logging or sending to a telemetry service

    def generate_report(self):
        return f"[Telemetry Report] {self.data.__dict__.__repr__()}"


class OperationSpan:
    def __init__(self, telemetry: Telemetry, operation_name: str):
        self.telemetry = telemetry
        self.operation_name = operation_name
        self.start_time = None

    def __enter__(self):
        self.start_time = time.time()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.start_time:
            self.telemetry.data.operation_latency[self.operation_name] += time.time() - self.start_time
