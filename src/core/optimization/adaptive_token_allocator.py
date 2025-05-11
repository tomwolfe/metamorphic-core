# src/core/optimization/adaptive_token_allocator.py
from z3 import *
from src.core.ethics.constraints import EthicalAllocationPolicy
from typing import List
from src.core.chunking.dynamic_chunker import CodeChunk
from src.core.exceptions import AllocationError
import logging

logger = logging.getLogger(__name__)

class TokenAllocator:
    def __init__(self, total_budget: int = 32000): # Increased default budget
        self.total_budget = total_budget
        self.solver = Optimize()
        self.policy = EthicalAllocationPolicy()
        # Removed hardcoded models

    def _model_cost(self, model_idx_var: IntNumRef, tokens_var: IntNumRef, models_list: list) -> ArithRef:
        """
        Calculates the cost for a given model and token count as a Z3 arithmetic expression.
        Cost = (tokens * cost_per_token) + (tokens^1.2 / 1000) (approximated as tokens*tokens / 1000 for Z3 simplicity)
        This version is fully symbolic with respect to model_idx_var.
        """
        if not models_list:
            # Should not happen if model_costs is provided
            return RealVal(0)

        # Build the nested If expression for symbolic cost calculation
        # Start with the cost of the last model as the final 'else'
        cost_expr = (tokens_var * models_list[-1]['cost_per_token']) + \
                    (tokens_var * tokens_var) / 1000.0

        for j in range(len(models_list) - 2, -1, -1):
            model_details = models_list[j]
            cost_for_this_model = (tokens_var * model_details['cost_per_token']) + \
                                  (tokens_var * tokens_var) / 1000.0
            cost_expr = If(model_idx_var == j, cost_for_this_model, cost_expr)

        return cost_expr


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

        # Log min/max constraints per chunk
        for i in allocations:
            constraint_str_min = f"tokens_{i} >= 100"
            logger.info(f"TokenAllocator: Adding constraint: {constraint_str_min}")
            self.solver.add(allocations[i] >= 100)  # Minimum token guarantee

            constraint_str_max = f"tokens_{i} <= 20000"
            logger.info(f"TokenAllocator: Adding constraint: {constraint_str_max}")
            self.solver.add(allocations[i] <= 20000) # Max per chunk

        # Log model index constraints
        for i in range(len(chunks)):
            constraint_model_idx_min = f"model_{i} >= 0"
            logger.info(f"TokenAllocator: Adding constraint: {constraint_model_idx_min}")
            self.solver.add(model_vars[i] >= 0)

            constraint_model_idx_max = f"model_{i} < {len(models)}"
            logger.info(f"TokenAllocator: Adding constraint: {constraint_model_idx_max}")
            self.solver.add(model_vars[i] < len(models))


        # Model capacity constraints - Ensure allocated tokens are within model's effective length
        for i in range(len(chunks)):
            # Log model capacity constraints
            constraint_model_capacity_str = "Or([And(model_vars[{i}] == {j}, allocations[{i}] <= {models[j]['effective_length']}) for {j} in range(len(models))])"
            logger.info(f"TokenAllocator: Adding model capacity constraint for chunk {i}: {constraint_model_capacity_str}")
            self.solver.add(Or([
                And(model_vars[i] == j, allocations[i] <= models[j]['effective_length'])
                for j in range(len(models))
            ]))

        # Ethical constraints
        logger.info("TokenAllocator: Applying EthicalAllocationPolicy...")
        self.policy.apply(self.solver, allocations, model_vars)
        logger.info("TokenAllocator: Finished applying EthicalAllocationPolicy.")


        # Optimization objectives
        if self.solver.check() == sat:
            logger.info(f"TokenAllocator: Solver check SAT.")
            # No longer need solver_model_snapshot before minimization for _model_cost

            cost_terms = [self._model_cost(model_vars[i], allocations[i], models)
                          for i in range(len(chunks))]
            cost = Sum(cost_terms)

            logger.info(f"TokenAllocator: Cost expression to minimize: {cost}")
            self.solver.minimize(cost)

            # Re-check satisfiability after adding minimization objective
            if self.solver.check() == sat:
                final_model_snapshot = self.solver.model() # Get the model after minimization
                logger.info(f"TokenAllocator: Solver model AFTER minimization: {final_model_snapshot}")
                final_allocation = {
                    i: (final_model_snapshot.eval(allocations[i]).as_long(),
                        models[final_model_snapshot.eval(model_vars[i]).as_long()]['name'])
                    for i in range(len(chunks))
                }
                logger.info(f"TokenAllocator: Final allocation: {final_allocation}")
                return final_allocation
            else:
                logger.error("TokenAllocator: Solver became UNSAT or UNKNOWN after adding minimization objective.")
                raise AllocationError("No ethical allocation possible after attempting to minimize cost.")
        else:
            logger.error("TokenAllocator: Solver check UNSAT or UNKNOWN before minimization.")
            raise AllocationError("No ethical allocation possible.") # Raise AllocationError here too