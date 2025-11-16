"""
SAT Solver - DIMACS-like Multi-instance Format
----------------------------------------------------------
Project 1: Tough Problems & The Wonderful World of NP

INPUT FORMAT (multi-instance file):
-----------------------------------
Each instance starts with a comment and a problem definition:

c <instance_id> <k> <status?>
p cnf <n_vertices> <n_edges>
u,v
x,y
...

Example:
c 1 3 ?
p cnf 4 5
1,2
1,3
2,3
2,4
3,4
c 2 2 ?
p cnf 3 3
1,2
2,3
1,3

OUTPUT:
-------
A CSV file named 'resultsfile.csv' with columns:
instance_id,n_vars,n_clauses,method,satisfiable,time_seconds,solution


EXAMPLE OUTPUT
------------
instance_id,n_vars,n_clauses,method,satisfiable,time_seconds,solution
3,4,10,U,0.00024808302987366915,BruteForce,{}
4,4,10,S,0.00013304100139066577,BruteForce,"{1: True, 2: False, 3: False, 4: False}"
"""

from typing import List, Tuple, Dict
from src.helpers.sat_solver_helper import SatSolverAbstractClass
import itertools


class SatSolver(SatSolverAbstractClass):

    """
        NOTE: The output of the CSV file should be same as EXAMPLE OUTPUT above otherwise you will loose marks
        For this you dont need to save anything just make sure to return exact related output.
        
        For ease look at the Abstract Solver class and basically we are having the run method which does the saving
        of the CSV file just focus on the logic
    """


    def sat_backtracking(self, n_vars:int, clauses:List[List[int]]) -> Tuple[bool, Dict[int, bool]]:
        # Evaluate a single clause under an assignment.
        def eval_clause(clause, assignment: Dict[int, bool]):
            has_unassigned = False
            for lit in clause:
                var = abs(lit)
                if var in assignment:
                    val = assignment[var]
                    # satisfied
                    if (lit > 0 and val) or (lit < 0 and not val):
                        return True
                else:
                    has_unassigned = True
            # none was true
            if has_unassigned:
                return None
            else:
                # all evaluated to False
                return False

        # Check if current assignment  makes clause impossible
        def has_conflict(assignment: Dict[int, bool]) -> bool:
            for clause in clauses:
                res = eval_clause(clause, assignment)
                if res is False:
                    return True
            return False

        # Check if all clauses are already satisfied
        def all_clauses_satisfied(assignment: Dict[int, bool]) -> bool:
            if not clauses:
                return True
            for clause in clauses:
                res = eval_clause(clause, assignment)
                if res is not True:
                    return False
            return True

        # Prune if any clause is already impossible
        def backtrack(assignment: Dict[int, bool]) -> Tuple[bool, Dict[int, bool]]:
            if has_conflict(assignment):
                return False, {}

            # All clauses satisfied, so solution
            if all_clauses_satisfied(assignment):
                full_assign = assignment.copy()
                for v in range(1, n_vars + 1):
                    if v not in full_assign:
                        full_assign[v] = False
                return True, full_assign

            # Select next unasigned var
            next_var = None
            for v in range(1, n_vars + 1):
                if v not in assignment:
                    next_var = v
                    break

            # Brach fails
            if next_var is None:
                return False, {}

            for value in (True, False):
                assignment[next_var] = value
                sat, sol = backtrack(assignment)
                if sat:
                    return True, sol
                del assignment[next_var]

            return False, {}

        sat, sol = backtrack({})
        if sat:
            return True, sol
        else:
            return False, {}

    def sat_bruteforce(self, n_vars: int, clauses: List[List[int]]) -> Tuple[bool, Dict[int, bool]]:
        ## I decided to use dfs instead of itertools because I am unfamiliar with that library.
        ## It does generate all combinations (I didn't prune or backtrack so it is brute force)
        ## I simply dfs through all variable assignment.

        res = {}

        def evaluate_res(assignment: Dict[int, bool]) -> Tuple[bool, Dict[int, bool]]:
            # Check each clause
            for clause in clauses:
                satisfied = False
                for literal in clause:
                    var = abs(literal)
                    value = assignment[var]
                    if (literal > 0 and value) or (literal < 0 and not value):
                        satisfied = True
                        break
                if not satisfied:
                    return False, {}
            return True, assignment.copy()

        def dfs(var_index: int) -> Tuple[bool, Dict[int, bool]]:
            # Base case full assignment
            if var_index > n_vars:
                return evaluate_res(res)

            # Try False
            res[var_index] = False
            ok, sol = dfs(var_index + 1)
            if ok:
                return True, sol

            # Try True
            res[var_index] = True
            ok, sol = dfs(var_index + 1)
            if ok:
                return True, sol

            # No assignment worked
            return False, {}

        return dfs(1)

    #Implemented as a variation of Backtracking.
    def sat_bestcase(self, n_vars:int, clauses:List[List[int]]) -> Tuple[bool, Dict[int, bool]]:
        
        #evaluate single clause under an assignment
        def eval_clause(clause, assignment: Dict[int, bool]):
            has_unassigned = False

            for lit in clause:
                var = abs(lit)

                if var in assignment:
                    val = assignment[var]

                    if (lit > 0 and val) or (lit < 0 and not val):
                        return True
                else:
                    has_unassigned = True

            if has_unassigned:
                return None
            
            return False

        #check to see if current assignment makes clause impossible
        def has_conflict(assignment: Dict[int, bool]) -> bool:
            for clause in clauses:
                if eval_clause(clause, assignment) is False:
                    return True
                
            return False

        #check if we are done
        def all_clauses_satisfied(assignment: Dict[int, bool]) -> bool:
            if not clauses:
                return True
            
            for clause in clauses:
                if eval_clause(clause, assignment) is not True:
                    return False
                
            return True

        #fill in any unassigned variables with False so we have a complete assignment
        def fill_assignment(assignment: Dict[int, bool]) -> Dict[int, bool]:
            return {v: assignment.get(v, False) for v in range(1, n_vars + 1)}

        #count how many clauses are satisfied by this assignemnt, used for tracking
        def count_satisfied(assignment: Dict[int, bool]) -> int:
            total = 0

            for clause in clauses:
                if eval_clause(clause, assignment) is True:
                    total += 1
            return total

        #best so far assignemnt
        best_assignment: Dict[int, bool] = {}
        best_score = -1

        #store solution if found
        solution: Dict[int, bool] | None = None

        #given a partial assignment, extend it to see how many clauses it satisfies. If better than current best, record
        def record_candidate(candidate: Dict[int, bool]):
            nonlocal best_assignment, best_score
            filled = fill_assignment(candidate)
            score = count_satisfied(filled)
            if score > best_score:
                best_score = score
                best_assignment = filled.copy()

        #standard backtracking search, true is a satisfying assignment was found
        def backtrack(assignment: Dict[int, bool]) -> bool:
            nonlocal solution, best_assignment, best_score

            if has_conflict(assignment):
                record_candidate(assignment)
                return False

            if all_clauses_satisfied(assignment):
                solved = fill_assignment(assignment)
                best_assignment = solved.copy()
                best_score = len(clauses)
                solution = solved
                return True

            if len(assignment) == n_vars:
                record_candidate(assignment)
                return False

            next_var = None
            for v in range(1, n_vars + 1):
                if v not in assignment:
                    next_var = v
                    break
            if next_var is None:
                record_candidate(assignment)
                return False

            for value in (True, False):
                assignment[next_var] = value
                if backtrack(assignment):
                    return True
                del assignment[next_var]
            return False

        found = backtrack({})
        if found and solution is not None:
            return True, solution

        #return the best assignment we saw
        if not best_assignment:
            best_assignment = {v: False for v in range(1, n_vars + 1)}
        return False, best_assignment

    def sat_simple(self, n_vars:int, clauses:List[List[int]]) -> Tuple[bool, Dict[int, bool]]:
        pass
