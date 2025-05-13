# src/core/optimization/adaptive_token_allocator.py
from z3 import *
from src.core.ethics.constraints import EthicalAllocationPolicy
from typing import List, Dict # Ensure Dict is imported
from src.core.chunking.dynamic_chunker import CodeChunk
from src.core.exceptions import AllocationError
import logging

logger = logging.getLogger(__name__)

# --- ADDED CONSTANT ---
REALISTIC_MIN_TOKENS_PER_CHUNK = 1000 # Or another value like 500, 1500
# --- END ADDED CONSTANT ---

class TokenAllocator:
    def __init__(self, total_budget: int = 32000):
        self.total_budget = total_budget
        # self.solver = Optimize() # REMOVE instance creation from __init__
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
        # Further increase the quadratic divisor to make the penalty for more tokens much smaller,
        # encouraging the solver to use more tokens if the budget allows.
        # The previous value of 10,000,000 was still too punitive.
        quadratic_divisor = 1000000000.0 # Drastically increase divisor

        # Also, consider reducing the impact of the linear cost term,
        # as it might also contribute to favoring minimal tokens if cost_per_token is not small enough.
        # For now, focusing on the quadratic_divisor.
        # --- END MODIFICATION ---

        # Build the nested If expression for symbolic cost calculation
        # Start with the cost of the last model as the final 'else'
        # Ensure cost_per_token is treated as a very small factor if not zero
        base_linear_cost = ToReal(tokens_var) * (models_list[-1]['cost_per_token'] if models_list[-1]['cost_per_token'] > 0 else 1e-9)
        cost_expr = base_linear_cost + (ToReal(tokens_var) * ToReal(tokens_var)) / quadratic_divisor

        for j in range(len(models_list) - 2, -1, -1):
            model_details = models_list[j]
            linear_cost_term = ToReal(tokens_var) * (model_details['cost_per_token'] if model_details['cost_per_token'] > 0 else 1e-9)
            cost_for_this_model = linear_cost_term + \
                                   (ToReal(tokens_var) * ToReal(tokens_var)) / quadratic_divisor
            cost_expr = If(model_idx_var == j, cost_for_this_model, cost_expr)

        return cost_expr

    def allocate(self, chunks: List[CodeChunk], model_costs: Dict[str, Dict]) -> dict: # Ensure model_costs type hint is correct
        self.solver = Optimize() # CREATE NEW INSTANCE for each call

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
            # --- MODIFIED MINIMUM CONSTRAINT ---
            constraint_str_min = f"tokens_{i} >= {REALISTIC_MIN_TOKENS_PER_CHUNK}" # <-- MODIFIED
            logger.info(f"TokenAllocator: Adding constraint: {constraint_str_min}")
            self.solver.add(allocations[i] >= REALISTIC_MIN_TOKENS_PER_CHUNK) # <-- MODIFIED
            # --- END MODIFIED MINIMUM CONSTRAINT ---

            constraint_str_max = f"tokens_{i} <= 20000" # This can be adjusted based on model context windows
            logger.info(f"TokenAllocator: Adding constraint: {constraint_str_max}")
            self.solver.add(allocations[i] <= 20000)

        for i in range(len(chunks)):
            # --- FIX START: Correct f-string construction for logging ---
            conditions_str_list = []
            for k_idx in range(len(models)):
                conditions_str_list.append(f"And(model_vars[{i}] == {k_idx}, allocations[{i}] <= {models[k_idx]['effective_length']})")
            constraint_model_capacity_str = f"Or([{', '.join(conditions_str_list)}])"
            # --- FIX END ---
            logger.info(f"TokenAllocator: Adding model capacity constraint for chunk {i}: {constraint_model_capacity_str}")
            self.solver.add(Or([
                And(model_vars[i] == j_loop_var, allocations[i] <= models[j_loop_var]['effective_length']) # Renamed loop var for clarity
                for j_loop_var in range(len(models))
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
            else: # Minimization failed
                logger.error("TokenAllocator: Solver became UNSAT or UNKNOWN after adding minimization objective.")
                # Fallback: try to find *any* solution without minimizing cost if minimization fails
                self.solver = Optimize() # Create a new Optimize instance for fallback
                # Re-add all constraints
                self.solver.add(Sum([allocations[i] for i in range(len(chunks))]) <= self.total_budget)
                for i in allocations:
                    # --- MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
                    self.solver.add(allocations[i] >= REALISTIC_MIN_TOKENS_PER_CHUNK) # <-- MODIFIED
                    # --- END MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
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
        else: # Initial solver check was UNSAT or UNKNOWN
            logger.error("TokenAllocator: Solver check UNSAT or UNKNOWN before minimization.")
            # --- START FIX for Failure 2 ---
            logger.info("TokenAllocator: Attempting fallback allocation without cost minimization due to initial UNSAT.")
            self.solver = Optimize() # Create a new Optimize instance for fallback
            # Re-add all constraints (same as in the other fallback block)
            self.solver.add(Sum([allocations[i] for i in range(len(chunks))]) <= self.total_budget)
            for i in allocations:
                # --- MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
                self.solver.add(allocations[i] >= REALISTIC_MIN_TOKENS_PER_CHUNK) # <-- MODIFIED
                # --- END MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
                self.solver.add(allocations[i] <= 20000)
            for i in range(len(chunks)):
                self.solver.add(model_vars[i] >= 0)
                self.solver.add(model_vars[i] < len(models))
                self.solver.add(Or([And(model_vars[i] == j, allocations[i] <= models[j]['effective_length']) for j in range(len(models))]))
            self.policy.apply(self.solver, allocations, model_vars) # Re-apply policy

            if self.solver.check() == sat:
                logger.warning("TokenAllocator: Initial check failed, but found a feasible solution with fallback (no cost minimization).")
                fallback_model_snapshot = self.solver.model()
                final_allocation = {
                    i: (fallback_model_snapshot.eval(allocations[i]).as_long(),
                        models[fallback_model_snapshot.eval(model_vars[i]).as_long()]['name'])
                    for i in range(len(chunks))
                }
                logger.info(f"TokenAllocator: Fallback allocation (initial UNSAT): {final_allocation}")
                return final_allocation
            else:
                logger.error("TokenAllocator: Fallback allocation also failed after initial UNSAT.")
                raise AllocationError("No ethical allocation possible even without cost minimization.")