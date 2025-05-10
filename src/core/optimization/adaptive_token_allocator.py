from z3 import *
from src.core.ethics.constraints import EthicalAllocationPolicy
from typing import List
from src.core.chunking.dynamic_chunker import CodeChunk
from src.core.exceptions import AllocationError
import logging

logger = logging.getLogger(__name__)

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

        # Log initial information
        logger.info(f"TokenAllocator: Starting allocation for {len(chunks)} chunks with total_budget: {self.total_budget}")

        # Hard constraints
        constraint_str_sum = f"Sum(list(allocations.values())) <= {self.total_budget}"
        logger.info(f"TokenAllocator: Adding constraint: {constraint_str_sum}")
        self.solver.add(Sum(list(allocations.values())) <= self.total_budget)

        # More constraint logging here

        self.solver.add([allocations[i] >= 100 for i in allocations])

        # Model capacity constraints - Ensure allocated tokens are within model's effective length
        for i in range(len(chunks)):
            self.solver.add(Or([
                And(model_vars[i] == j, allocations[i] <= models[j]['effective_length'])
                for j in range(len(models))
            ]))

        # Ethical constraints
        logger.info("TokenAllocator: Applying EthicalAllocationPolicy...")
        self.policy.apply(self.solver, allocations, model_vars)

        # Optimization objectives
        if self.solver.check() == sat:
            #Log the z3 model to see how z3 solved.
            logger.info(f"TokenAllocator: Solver model BEFORE minimization: {self.solver.model()}")

            model = self.solver.model()

            # Log model here
            cost = Sum([self._model_cost(model_vars[i], allocations[i], model, models) # Pass solver model to _model_cost and models
                       for i in range(len(chunks))])
            self.solver.minimize(cost)
            logger.info(f"TokenAllocator: Minimize cost expression {cost}")


            final_allocation = { # ... rest of the return logic remains the same
                i: (model.eval(allocations[i]).as_long(),
                    models[model.eval(model_vars[i]).as_long()]['name'])
                for i in range(len(chunks))
            }

            logger.info(f"TokenAllocator: Final allocation: {final_allocation}") # Log the final allocation

            return final_allocation
        raise AllocationError("No ethical allocation possible")