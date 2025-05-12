# src/core/optimization/adaptive_token_allocator.py
from z3 import *
from src.core.ethics.constraints import EthicalAllocationPolicy
from typing import List, Dict # Ensure Dict is imported
from src.core.chunking.dynamic_chunker import CodeChunk
from src.core.exceptions import AllocationError
import logging

logger = logging.getLogger(__name__)

class TokenAllocator:
    def __init__(self, total_budget: int = 32000):
        self.total_budget = total_budget
        self.solver = Optimize()
        self.policy = EthicalAllocationPolicy()

    def _model_cost(self, model_idx_var: IntNumRef, tokens_var: IntNumRef, models_list: list) -> ArithRef:
        """
        Calculates the cost for a given model and token count as a Z3 arithmetic expression.
        Cost = (tokens * cost_per_token) + (tokens^2 / coefficient)
        """
        if not models_list:
            return RealVal(0)

        # --- MODIFIED QUADRATIC TERM COEFFICIENT ---
        # Original divisor: 1000.0
        # New, less punitive divisor:
        quadratic_divisor = 10000000.0 # Significantly larger divisor to reduce quadratic penalty
        # --- END MODIFICATION ---

        # Build the nested If expression for symbolic cost calculation
        # Start with the cost of the last model as the final 'else'
        cost_expr = (ToReal(tokens_var) * models_list[-1]['cost_per_token']) + \
                    (ToReal(tokens_var) * ToReal(tokens_var)) / quadratic_divisor

        for j in range(len(models_list) - 2, -1, -1):
            model_details = models_list[j]
            cost_for_this_model = (ToReal(tokens_var) * model_details['cost_per_token']) + \
                                  (ToReal(tokens_var) * ToReal(tokens_var)) / quadratic_divisor
            cost_expr = If(model_idx_var == j, cost_for_this_model, cost_expr)
        
        return cost_expr

    def allocate(self, chunks: List[CodeChunk], model_costs: Dict[str, Dict]) -> dict: # Ensure model_costs type hint is correct
        # Reset solver for fresh allocation
        self.solver.reset() # Add this line to ensure solver is fresh for each call

        models = [
            {'name': name, **details}
            for name, details in model_costs.items()
        ]
        allocations = {i: Int(f'tokens_{i}') for i in range(len(chunks))}
        model_vars = {i: Int(f'model_{i}') for i in range(len(chunks))}

        logger.info(f"TokenAllocator: Starting allocation for {len(chunks)} chunks with total_budget: {self.total_budget}")

        constraint_str_sum = f"Sum([allocations[i] for i in range({len(chunks)})]) <= {self.total_budget}"
        logger.info(f"TokenAllocator: Adding constraint: {constraint_str_sum}")
        self.solver.add(Sum([allocations[i] for i in range(len(chunks))]) <= self.total_budget)


        for i in allocations:
            constraint_str_min = f"tokens_{i} >= 100"
            logger.info(f"TokenAllocator: Adding constraint: {constraint_str_min}")
            self.solver.add(allocations[i] >= 100)

            constraint_str_max = f"tokens_{i} <= 20000" # This can be adjusted based on model context windows
            logger.info(f"TokenAllocator: Adding constraint: {constraint_str_max}")
            self.solver.add(allocations[i] <= 20000)

        for i in range(len(chunks)):
            constraint_model_idx_min = f"model_{i} >= 0"
            logger.info(f"TokenAllocator: Adding constraint: {constraint_model_idx_min}")
            self.solver.add(model_vars[i] >= 0)

            constraint_model_idx_max = f"model_{i} < {len(models)}"
            logger.info(f"TokenAllocator: Adding constraint: {constraint_model_idx_max}")
            self.solver.add(model_vars[i] < len(models))

        for i in range(len(chunks)):
            constraint_model_capacity_str = f"Or([And(model_vars[{i}] == {j}, allocations[{i}] <= {models[j]['effective_length']}) for j in range({len(models)})])"
            logger.info(f"TokenAllocator: Adding model capacity constraint for chunk {i}: {constraint_model_capacity_str}")
            self.solver.add(Or([
                And(model_vars[i] == j, allocations[i] <= models[j]['effective_length'])
                for j in range(len(models))
            ]))

        logger.info("TokenAllocator: Applying EthicalAllocationPolicy...")
        self.policy.apply(self.solver, allocations, model_vars)
        logger.info("TokenAllocator: Finished applying EthicalAllocationPolicy.")

        if self.solver.check() == sat:
            logger.info(f"TokenAllocator: Solver check SAT.")
            
            cost_terms = [self._model_cost(model_vars[i], allocations[i], models)
                          for i in range(len(chunks))]
            total_cost_objective = Sum(cost_terms)
            
            logger.info(f"TokenAllocator: Cost expression to minimize: {total_cost_objective}")
            self.solver.minimize(total_cost_objective)

            if self.solver.check() == sat:
                final_model_snapshot = self.solver.model()
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
                # Fallback: try to find *any* solution without minimizing cost if minimization fails
                self.solver.reset() # Reset to remove minimization objective
                # Re-add all constraints
                self.solver.add(Sum([allocations[i] for i in range(len(chunks))]) <= self.total_budget)
                for i in allocations:
                    self.solver.add(allocations[i] >= 100)
                    self.solver.add(allocations[i] <= 20000)
                for i in range(len(chunks)):
                    self.solver.add(model_vars[i] >= 0)
                    self.solver.add(model_vars[i] < len(models))
                    self.solver.add(Or([And(model_vars[i] == j, allocations[i] <= models[j]['effective_length']) for j in range(len(models))]))
                self.policy.apply(self.solver, allocations, model_vars) # Re-apply policy

                if self.solver.check() == sat:
                    logger.warning("TokenAllocator: Cost minimization failed, but found a feasible solution without minimization.")
                    fallback_model_snapshot = self.solver.model()
                    final_allocation = {
                        i: (fallback_model_snapshot.eval(allocations[i]).as_long(),
                            models[fallback_model_snapshot.eval(model_vars[i]).as_long()]['name'])
                        for i in range(len(chunks))
                    }
                    logger.info(f"TokenAllocator: Fallback allocation (no cost minimization): {final_allocation}")
                    return final_allocation
                else:
                    logger.error("TokenAllocator: Solver still UNSAT/UNKNOWN even without cost minimization.")
                    raise AllocationError("No ethical allocation possible even without cost minimization.")
        else:
            logger.error("TokenAllocator: Solver check UNSAT or UNKNOWN before minimization.")
            raise AllocationError("No ethical allocation possible with initial constraints.")