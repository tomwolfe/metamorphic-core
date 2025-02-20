from z3 import *
from src.core.ethics.constraints import EthicalAllocationPolicy
from typing import List
from src.core.chunking.dynamic_chunker import CodeChunk
from src.core.exceptions import AllocationError

class TokenAllocator:
    def __init__(self, total_budget: int = 32000):
        self.solver = Optimize()
        self.policy = EthicalAllocationPolicy()
        self.models = [
            {'name': 'gemini', 'cost_per_token': 0.000001, 'effective_length': 32000}, # Example rates/lengths
            {'name': 'gpt-4', 'cost_per_token': 0.00003, 'effective_length': 8000},
            {'name': 'mistral-large', 'cost_per_token': 0.000002, 'effective_length': 32000}
        ]

    def allocate(self, chunks: List[CodeChunk]) -> dict:
        allocations = {i: Int(f'tokens_{i}') for i in range(len(chunks))}
        model_vars = {i: Int(f'model_{i}') for i in range(len(chunks))}

        # Hard constraints
        self.solver.add(Sum(list(allocations.values())) <= self.total_budget)
        self.solver.add([allocations[i] >= 100 for i in allocations])
        self.solver.add([model_vars[i] >= 0 for i in range(len(chunks))])
        self.solver.add([model_vars[i] < len(self.models) for i in range(len(chunks))])


        # Ethical constraints
        self.policy.apply(self.solver, allocations, model_vars, self.models)

        # Optimization objectives
        cost = Sum([self._model_cost(model_vars[i], allocations[i])
                   for i in range(len(chunks))])
        self.solver.minimize(cost)

        if self.solver.check() == sat:
            model = self.solver.model()
            return {
                i: (model[allocations[i]].as_long(),
                    self.models[model[model_vars[i]].as_long()]['name'])
                for i in range(len(chunks))
            }
        raise AllocationError("No ethical allocation possible")

    def _model_cost(self, model_idx: int, tokens: int) -> float:
        model = self.models[model_idx]
        base_cost = tokens * model['cost_per_token']
        complexity_penalty = (tokens ** 1.2) / 1000  # Example non-linear penalty
        return base_cost + complexity_penalty
