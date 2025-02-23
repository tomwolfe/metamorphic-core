# src/core/monitoring/telemetry.py
from dataclasses import dataclass
from typing import Dict, ContextManager
from contextlib import contextmanager
from collections import defaultdict
import time

@dataclass
class TelemetryData:
    token_usage: Dict[str, int]
    model_usage: Dict[str, int]
    ethical_checks: int
    operation_latency: Dict[str, float]
    constraint_violations: Dict[str, int]

class Telemetry:
    def __init__(self):
        self.start_session() # Initialize with empty data
        self.data = TelemetryData(
            token_usage=defaultdict(int),
            model_usage=defaultdict(int),
            ethical_checks=0,
            operation_latency=defaultdict(float),
            constraint_violations=defaultdict(int)
        )

    def start_session(self):
        """Reset metrics for new session"""
        self.data = TelemetryData(
            token_usage=defaultdict(int),
            model_usage=defaultdict(int),
            ethical_checks=0,
            operation_latency=defaultdict(float),
            constraint_violations=defaultdict(int)
        )


    def track(self, metric: str, value: int=1, tags: dict = None):
        if tags is None:
            tags = {}
        if metric.startswith('tokens_'):
            self.data.token_usage[metric] += value
        elif metric.startswith('model_'):
            self.data.model_usage[metric] += value
        elif metric == 'ethical_check':
            self.data.ethical_checks += value
        elif metric == 'operation_latency':
            operation_name = tags.get('operation', 'unknown')
            self.data.operation_latency[operation_name] = tags.get('duration_ms', 0)
        elif metric == 'constraint_violation': # Track constraint violations
            constraint_name = tags.get('constraint', 'unknown')
            self.data.constraint_violations[constraint_name] += value


    @contextmanager
    def span(self, operation_name: str) -> ContextManager[None]:
        start_time = time.time()
        yield # Context block executes here
        duration = time.time() - start_time
        self.track('operation_latency', tags={'operation': operation_name, 'duration_ms': int(duration * 1000)})

    def publish(self):
        # Integration with monitoring backend
        print(f"[Telemetry Report] {self.data}")

