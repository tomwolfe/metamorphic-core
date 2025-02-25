from z3 import *
from src.core.ethics.constraints import EthicalAllocationPolicy
from typing import List
from src.core.chunking.dynamic_chunker import CodeChunk
from src.core.exceptions import AllocationError

class TokenAllocator:
    def __init__(self, total_budget: int = 32000):
        self.total_budget = total_budget
        self.solver = Optimize()
        self.policy = EthicalAllocationPolicy()
        # Removed hardcoded models

    def allocate(self, chunks: List[CodeChunk], model_costs: dict) -> dict:
        models = [
            {'name': name, **details}
            for name, details in model_costs.items()
        ]
        allocations = {i: Int(f'tokens_{i}') for i in range(len(chunks))}
        model_vars = {i: Int(f'model_{i}') for i in range(len(chunks))}

        # Hard constraints
        self.solver.add(Sum(list(allocations.values())) <= self.total_budget)
        self.solver.add([allocations[i] >= 100 for i in allocations])
        self.solver.add([model_vars[i] >= 0 for i in range(len(chunks))])
        self.solver.add([model_vars[i] < len(models) for i in range(len(chunks))])


        # Ethical constraints
        self.policy.apply(self.solver, allocations, model_vars)

        # Optimization objectives
        if self.solver.check() == sat:
            model = self.solver.model() # Assign model BEFORE list comprehension - Moved this line UP

            # Optimization objectives - 'model' is now defined before this line
            cost = Sum([self._model_cost(model_vars[i], allocations[i], model, models) # Pass solver model to _model_cost and models
                       for i in range(len(chunks))])
            self.solver.minimize(cost)


            return { # ... rest of the return logic remains the same
                i: (model.eval(allocations[i]).as_long(),
                    models[model.eval(model_vars[i]).as_long()]['name'])
                for i in range(len(chunks))
            }
        raise AllocationError("No ethical allocation possible")

    def _model_cost(self, model_idx: int, tokens: int, model: ModelRef, models: list) -> float: # Added models: list parameter
        # Ensure model_idx is an integer by evaluating the Z3 expression # Added model.eval() to convert to integer
        evaluated_model_idx = model.eval(model_idx).as_long() # Convert model_idx to integer # Added model.eval()
        selected_model = models[evaluated_model_idx] # Use the integer index
        base_cost = tokens * selected_model['cost_per_token']
        complexity_penalty = (tokens ** 1.2) / 1000  # Example non-linear penalty
        return base_cost + complexity_penalty

