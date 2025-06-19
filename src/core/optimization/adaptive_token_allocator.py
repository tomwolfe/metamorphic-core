# src/core/optimization/adaptive_token_allocator.py
from z3 import *
from src.core.ethics.constraints import EthicalAllocationPolicy
from typing import List, Dict
from src.core.chunking.dynamic_chunker import CodeChunk
from src.core.exceptions import AllocationError
import logging
from z3 import Real # Ensure Real is imported

logger = logging.getLogger(__name__) # FIX: Corrected logger name

# Increased minimum token allocation per chunk to leverage larger model capacities.
# This value defines the minimum tokens per chunk and must be compatible with all LLM capacities.
# Task 1.8.1b suggested "e.g., 1000" as a suitable minimum.
REALISTIC_MIN_TOKENS_PER_CHUNK = 1000

class TokenAllocator:
    # --- START OF CHANGE 1 ---
    def __init__(self, total_budget: int = 500000): # Increased budget significantly, FIX: __init__
        self.total_budget = total_budget
        # self.solver = Optimize() # REMOVE instance creation from init
        self.policy = EthicalAllocationPolicy()
    # --- END OF CHANGE 1 ---

    def allocate(self, chunks: List[CodeChunk], model_costs: Dict[str, Dict]) -> dict: # Ensure model_costs type hint is correct
        self.solver = Optimize() # CREATE NEW INSTANCE for each call

        models = [
            {'name': name, **details}
            for name, details in model_costs.items()
        ]
        allocations = {i: Int(f'tokens_{i}') for i in range(len(chunks))}
        model_vars = {i: Int(f'model_{i}') for i in range(len(chunks))} # Define model_vars here

        # Add warning if only one model is available for allocation
        if len(models) == 1:
            logger.warning(
                "TokenAllocator: Only one model provider ({}) is available for allocation after configuration. ".format(models[0]['name']) +
                "Model diversity constraints in EthicalAllocationPolicy will be naturally bypassed."
            )

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

            # --- START OF CHANGE 2 ---
            # This is a hard cap per chunk for input context. Increase it significantly.
            constraint_str_max = f"tokens_{i} <= 100000" # <-- INCREASED FROM 20000
            logger.info(f"TokenAllocator: Adding constraint: {constraint_str_max}")
            self.solver.add(allocations[i] <= 100000) # <-- INCREASED FROM 20000
            # --- END OF CHANGE 2 ---

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

            # Objective is to MAXIMIZE total tokens allocated within the budget
            total_tokens = Sum([allocations[i] for i in range(len(chunks))])
            logger.info(f"TokenAllocator: Objective to maximize total tokens: {total_tokens}")
            self.solver.maximize(total_tokens)

            if self.solver.check() == sat: # Check again after adding the objective
                final_model_snapshot = self.solver.model() 
                logger.info(f"TokenAllocator: Solver model AFTER maximization: {final_model_snapshot}") # Corrected log message
                final_allocation = {
                    i: (final_model_snapshot.eval(allocations[i]).as_long(),
                        models[final_model_snapshot.eval(model_vars[i]).as_long()]['name'])
                    for i in range(len(chunks))
                }
                logger.info(f"TokenAllocator: Final allocation: {final_allocation}")
                return final_allocation
            else: # Maximization failed, which is a critical error
                logger.error("TokenAllocator: Solver became UNSAT or UNKNOWN after adding maximization objective. This indicates a conflict in constraints.")
                # Fallback: try to find *any* solution without maximizing tokens if maximization fails
                self.solver = Optimize() # Create a new Optimize instance for fallback
                # Re-declare Z3 variables for the new solver instance
                allocations = {i: Int(f'tokens_{i}') for i in range(len(chunks))}
                model_vars = {i: Int(f'model_{i}') for i in range(len(chunks))}
                # Re-add all constraints
                self.solver.add(Sum([allocations[i] for i in range(len(chunks))]) <= self.total_budget)
                for i in allocations:
                    # --- MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
                    self.solver.add(allocations[i] >= REALISTIC_MIN_TOKENS_PER_CHUNK) # <-- MODIFIED
                    # --- END MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
                    self.solver.add(allocations[i] <= 100000) # <-- MODIFIED
                for i in range(len(chunks)):
                    self.solver.add(model_vars[i] >= 0)
                    self.solver.add(model_vars[i] < len(models))
                    self.solver.add(Or([And(model_vars[i] == j, allocations[i] <= models[j]['effective_length']) for j in range(len(models))]))
                self.policy.apply(self.solver, allocations, model_vars) # Re-apply policy

                if self.solver.check() == sat:
                    logger.warning("TokenAllocator: Maximization failed, but found a feasible solution without an objective.")
                    fallback_model_snapshot = self.solver.model()
                    final_allocation = {
                        i: (fallback_model_snapshot.eval(allocations[i]).as_long(),
                            models[fallback_model_snapshot.eval(model_vars[i]).as_long()]['name'])
                        for i in range(len(chunks))
                    }
                    logger.info(f"TokenAllocator: Fallback allocation (no token maximization): {final_allocation}")
                    return final_allocation 
                else:
                    logger.error("TokenAllocator: Solver still UNSAT/UNKNOWN even without token maximization (after maximization failure).")
                    raise AllocationError("No ethical allocation possible even without token maximization.")
        else: # Initial solver check was UNSAT or UNKNOWN 
            logger.error("TokenAllocator: Solver check UNSAT or UNKNOWN before maximization.")
            # --- START FIX for Failure 2 ---
            logger.info("TokenAllocator: Attempting fallback allocation without token maximization due to initial UNSAT.")
            self.solver = Optimize() # Create a new Optimize instance for fallback
            # Re-declare Z3 variables for the new solver instance
            allocations = {i: Int(f'tokens_{i}') for i in range(len(chunks))}
            model_vars = {i: Int(f'model_{i}') for i in range(len(chunks))}
            # Re-add all constraints (same as in the other fallback block)
            self.solver.add(Sum([allocations[i] for i in range(len(chunks))]) <= self.total_budget)
            for i in allocations:
                # --- MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
                self.solver.add(allocations[i] >= REALISTIC_MIN_TOKENS_PER_CHUNK) # <-- MODIFIED
                # --- END MODIFIED MINIMUM CONSTRAINT IN FALLBACK ---
                self.solver.add(allocations[i] <= 100000) # <-- MODIFIED
            for i in range(len(chunks)):
                self.solver.add(model_vars[i] >= 0)
                self.solver.add(model_vars[i] < len(models))
                self.solver.add(Or([And(model_vars[i] == j, allocations[i] <= models[j]['effective_length']) for j in range(len(models))]))
            self.policy.apply(self.solver, allocations, model_vars) # Re-apply policy

            if self.solver.check() == sat:
                logger.warning("TokenAllocator: Initial check failed, but found a feasible solution with fallback (no token maximization).")
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
                raise AllocationError("No ethical allocation possible even without token maximization.") # FIX: Raise error here

    # --- ADDED METHOD: _model_cost ---
    def _model_cost(self, chunk_idx: int, model_idx: int) -> Real:
        """Internal method to calculate cost for a chunk-model pair.
        This is a stub for testing purposes when the actual cost calculation is not the focus."""
        return Real(f"mock_cost_term_{chunk_idx}_{model_idx}") # Return a unique Z3 Real variable for mocking