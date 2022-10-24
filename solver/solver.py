import os
import time
import json
from collections import OrderedDict

# needs in VSIDS decider
from solver.priorityQueue import PriorityQueue


class Statistics:
    """
    Class used to store the various statistics measuerd while solving
    the SAT problem and defines method to print the statistics.
    """

    def __init__(self):
        self._input_file = ""
        self._result = ""
        self._output_assignment_file = ""
        self._num_vars = 0
        self._num_orig_clauses = 0
        self._num_clauses = 0
        self._num_learned_clauses = 0
        self._num_decisions = 0
        self._num_implications = 0
        self._start_time = 0
        self._read_time = 0
        self._complete_time = 0

    def print_stats(self):
        print("=========================== STATISTICS ===============================")
        print("Solving formula from file: ", self._input_file)
        print(f"Vars:{self._num_vars}, Clauses:{self._num_orig_clauses} Stored Clauses:{self._num_clauses}")
        print("Input Reading Time: ", self._read_time - self._start_time)
        print("-------------------------------")
        print("Learned clauses: ", self._num_learned_clauses)
        print("Decisions made: ", self._num_decisions)
        print("Implications made: ", self._num_implications)
        print("All time: ", self._complete_time - self._start_time)
        print("RESULT: ", self._result)
        if self._result == "SAT":
            print("Satisfying Assignment stored in file: ", self._output_assignment_file)
        print("=" * 70)


class AssignedNode:
    def __init__(self, var, value, level, clause):
        self.var = var
        self.value = value
        self.level = level
        self.clause = clause
        self.index = -1

    def __str__(self):
        return "Var: {} Val: {} Lev: {} Cls: {} Ind: {} ".format(
                self.var, self.value,self.level, self.clause, self.index)


class SAT:
    def __init__(self, to_log, decider):
        self._num_clauses = 0
        self._num_vars = 0
        self._level = 0
        self._nodes_variable = {}
        self._clauses = []
        self._stack_of_decision = []
        self._clauses_watched_by_l = {}
        self._literals_watching_c = {}
        self._is_log = to_log
        if decider not in ["ORDERED", "VSIDS"]:
            raise ValueError('The decider must be one from the list ["ORDERED","VSIDS"]')
        self._decider = decider
        self.stats = Statistics()

    def _is_negative_literal(self, literal):
        return literal > self._num_vars

    def _get_literal_var(self, literal):
        if self._is_negative_literal(literal):
            return literal - self._num_vars
        return literal

    def _add_clause(self, clause):
        clause = clause[:-1]
        clause = list(OrderedDict.fromkeys(clause))
        if len(clause) == 1:
            # Get the literal
            lit = clause[0]
            value_to_set = True

            if lit[0] == '-':
                value_to_set = False
                var = int(lit[1:])
            else:
                var = int(lit)

            if var not in self._nodes_variable:
                self.stats._num_implications += 1
                node = AssignedNode(var, value_to_set, 0, None)
                self._nodes_variable[var] = node
                self._stack_of_decision.append(node)

                node.index = len(self._stack_of_decision) - 1
                if self._is_log:
                    print("Implied(unary): ", node)
            else:
                node = self._nodes_variable[var]
                if node.value != value_to_set:
                    self.stats._result = "UNSAT"
                    return 0
            return 1

        clause_with_literals = []

        for lit in clause:
            if lit[0] == '-':
                var = int(lit[1:])
                clause_with_literals.append(var + self._num_vars)
                if self._decider == "VSIDS":
                    self._lit_scores[var + self._num_vars] += 1
            else:
                var = int(lit)
                clause_with_literals.append(var)
                if self._decider == "VSIDS":
                    self._lit_scores[var] += 1
        clause_id = self._num_clauses
        self._clauses.append(clause_with_literals)
        self._num_clauses += 1
        watch_literal1 = clause_with_literals[0]
        watch_literal2 = clause_with_literals[1]

        self._literals_watching_c[clause_id] = [watch_literal1, watch_literal2]
        self._clauses_watched_by_l.setdefault(watch_literal1, []).append(clause_id)
        self._clauses_watched_by_l.setdefault(watch_literal2, []).append(clause_id)
        return 1

    def _read_file(self, cnf_filename):
        cnf_file = open(cnf_filename, "r")
        lines = [
            line.strip().split() for line in cnf_file.readlines()
            if (not (line.startswith('c') or
                     line.startswith('%') or
                     line.startswith('0'))
                and line != '\n')
        ]
        for line in lines:
            first_word = line[0]
            if first_word == "p":
                self._num_vars = int(line[2])
                if self._decider == "VSIDS":
                    self._lit_scores = [0 for i in range(0, 2 * self._num_vars + 1)]
                self.stats._num_orig_clauses = int(line[3])
            else:
                ret = self._add_clause(line)
                if ret == 0:
                    break

        if self._decider == "VSIDS":
            self._priority_queue = PriorityQueue(self._lit_scores)
            self._incr = 1

            for node in self._stack_of_decision:
                self._priority_queue.remove(node.var)
                self._priority_queue.remove(node.var + self._num_vars)
        cnf_file.close()

    def _decide(self):
        var = 0
        value_to_set = False
        if self._decider == "ORDERED":
            var = -1
            for x in range(1, self._num_vars + 1):
                if x not in self._nodes_variable:
                    var = x
                    break

            value_to_set = True

        elif self._decider == "VSIDS":
            literal = self._priority_queue.get_top()

            if literal == -1:
                var = -1
            else:
                var = self._get_literal_var(literal)

                is_neg_literal = self._is_negative_literal(literal)

                value_to_set = not is_neg_literal

                if is_neg_literal:
                    self._priority_queue.remove(var)
                else:
                    self._priority_queue.remove(var + self._num_vars)
        if var == -1:
            return -1
        # Increase the level by 1
        self._level += 1
        new_node = AssignedNode(var, value_to_set, self._level, None)
        self._nodes_variable[var] = new_node
        self._stack_of_decision.append(new_node)
        new_node.index = len(self._stack_of_decision) - 1

        # Increase the number of decisions
        self.stats._num_decisions += 1

        # Log if _is_log is true
        if self._is_log:
            print("Choosen decision: ", end="")
            print(new_node)
        return var

    def _unit_propagate(self, is_first_time):
        last_assignment_pointer = len(self._stack_of_decision) - 1
        if is_first_time:
            last_assignment_pointer = 0
        while last_assignment_pointer < len(self._stack_of_decision):
            last_assigned_node = self._stack_of_decision[last_assignment_pointer]
            if last_assigned_node.value:
                literal_that_is_falsed = last_assigned_node.var + self._num_vars
            else:
                literal_that_is_falsed = last_assigned_node.var
            itr = 0

            clauses_watched_by_falsed_literal = self._clauses_watched_by_l.setdefault(literal_that_is_falsed, []).copy()
            clauses_watched_by_falsed_literal.reverse()
            # conflict
            while itr < len(clauses_watched_by_falsed_literal):
                clause_id = clauses_watched_by_falsed_literal[itr]
                watch_list_of_clause = self._literals_watching_c[clause_id]

                other_watch_literal = watch_list_of_clause[0]
                if other_watch_literal == literal_that_is_falsed:
                    other_watch_literal = watch_list_of_clause[1]

                other_watch_var = self._get_literal_var(other_watch_literal)
                is_negative_other = self._is_negative_literal(other_watch_literal)

                if other_watch_var in self._nodes_variable:
                    value_assgned = self._nodes_variable[other_watch_var].value
                    if (is_negative_other and not value_assgned) or (
                            not is_negative_other and value_assgned):
                        itr += 1
                        continue

                new_literal_to_watch = -1
                clause = self._clauses[clause_id]

                for lit in clause:
                    if lit not in watch_list_of_clause:
                        var_of_lit = self._get_literal_var(lit)

                        if var_of_lit not in self._nodes_variable:
                            new_literal_to_watch = lit
                            break
                        else:
                            node = self._nodes_variable[var_of_lit]
                            is_negative = self._is_negative_literal(lit)
                            if (is_negative and not node.value) or (not is_negative and node.value):
                                new_literal_to_watch = lit
                                break

                if new_literal_to_watch != -1:
                    self._literals_watching_c[clause_id].remove(literal_that_is_falsed)
                    self._literals_watching_c[clause_id].append(new_literal_to_watch)
                    self._clauses_watched_by_l.setdefault(literal_that_is_falsed, []).remove(clause_id)
                    self._clauses_watched_by_l.setdefault(new_literal_to_watch, []).append(clause_id)

                else:
                    if other_watch_var not in self._nodes_variable:
                        value_to_set = not is_negative_other
                        assign_var_node = AssignedNode(other_watch_var, value_to_set, self._level, clause_id)
                        self._nodes_variable[other_watch_var] = assign_var_node
                        self._stack_of_decision.append(assign_var_node)
                        assign_var_node.index = len(self._stack_of_decision) - 1

                        if self._decider == "VSIDS":
                            self._priority_queue.remove(other_watch_var)
                            self._priority_queue.remove(other_watch_var + self._num_vars)

                        self.stats._num_implications += 1

                        if self._is_log:
                            print("Implied decision:", end="")
                            print(assign_var_node)
                    else:
                        conflict_node = AssignedNode(None, None, self._level, clause_id)
                        self._stack_of_decision.append(conflict_node)

                        conflict_node.index = len(self._stack_of_decision) - 1
                        if self._is_log:
                            print("CONFLICT")
                        return "CONFLICT"
                itr += 1
            last_assignment_pointer += 1
        return "NO_CONFLICT"

    def _binary_resolute(self, clause1, clause2, var):
        full_clause = clause1 + clause2

        full_clause = list(OrderedDict.fromkeys(full_clause))
        full_clause.remove(var)
        full_clause.remove(var + self._num_vars)
        return full_clause

    def _is_valid_clause(self, clause, level):
        counter = 0
        maxi = -1
        cand = -1

        for lit in clause:
            var = self._get_literal_var(lit)
            node = self._nodes_variable[var]

            if node.level == level:
                counter += 1
                if node.index > maxi:
                    maxi = node.index
                    cand = node

        # Conflict is valid if counter == 1, so return counter == 1
        return counter == 1, cand

    def _get_backtrack_level(self, conflict_clause, conflict_level):
        maximum_level_before_conflict_level = -1
        literal_at_conflict_level = -1

        for lit in conflict_clause:
            var = self._get_literal_var(lit)
            assigned_node = self._nodes_variable[var]

            if assigned_node.level == conflict_level:
                literal_at_conflict_level = lit
            else:
                if assigned_node.level > maximum_level_before_conflict_level:
                    maximum_level_before_conflict_level = assigned_node.level
        return maximum_level_before_conflict_level, literal_at_conflict_level

    def _analyze_conflict(self):
        assigment_stack_pointer = len(self._stack_of_decision) - 1
        conflict_node = self._stack_of_decision[assigment_stack_pointer]
        conflict_level = conflict_node.level
        conflict_clause = self._clauses[conflict_node.clause]

        self._stack_of_decision.pop()
        if self._is_log:
            print("Analyzing Conflict in the node: ", end="")
            print(conflict_node)

        if conflict_level == 0:
            return -1, None
        while True:
            is_nice, prev_assigned_node = self._is_valid_clause(conflict_clause, conflict_level)

            if is_nice:
                break
            if self._is_log:
                print("Clause: ", conflict_clause)
                print("Node_to_use ", prev_assigned_node)
            clause = self._clauses[prev_assigned_node.clause]
            var = prev_assigned_node.var
            conflict_clause = self._binary_resolute(conflict_clause, clause, var)

        if self._is_log:
            print("Conflict Clause: ", conflict_clause)

        if len(conflict_clause) > 1:
            self.stats._num_learned_clauses += 1
            clause_id = self._num_clauses
            self._num_clauses += 1
            self._clauses.append(conflict_clause)

            self._clauses_watched_by_l.setdefault(conflict_clause[0], []).append(clause_id)
            self._clauses_watched_by_l.setdefault(conflict_clause[1], []).append(clause_id)

            self._literals_watching_c[clause_id] = [conflict_clause[0], conflict_clause[1]]

            if self._decider == "VSIDS":
                for l in conflict_clause:
                    self._lit_scores[l] += self._incr
                    self._priority_queue.increase_update(l, self._incr)
                self._incr += 0.75

            backtrack_level, conflict_level_literal = self._get_backtrack_level(conflict_clause, conflict_level)

            conflict_level_var = self._get_literal_var(conflict_level_literal)

            is_negative_conflict_lit = self._is_negative_literal(conflict_level_literal)

            value_to_set = True
            if is_negative_conflict_lit:
                value_to_set = False
            node = AssignedNode(conflict_level_var, value_to_set, backtrack_level, clause_id)

            if self._is_log:
                print("Backtracking to level ", backtrack_level)
                print("Node after backtrack ", node)
            return backtrack_level, node
        else:
            literal = conflict_clause[0]
            var = self._get_literal_var(literal)
            is_negative_literal = self._is_negative_literal(literal)

            assigned_node = self._nodes_variable[var]
            backtrack_level = 0

            value_to_set = True
            if is_negative_literal:
                value_to_set = False
            node = AssignedNode(var, value_to_set, backtrack_level, None)
            return backtrack_level, node

    def _backtrack(self, backtrack_level, node_to_add):
        self._level = backtrack_level
        itr = len(self._stack_of_decision) - 1
        while True:
            if itr < 0:
                break
            if self._stack_of_decision[itr].level <= backtrack_level:
                break
            else:
                del self._nodes_variable[self._stack_of_decision[itr].var]

                node = self._stack_of_decision.pop(itr)

                if self._decider == "VSIDS":
                    self._priority_queue.add(node.var, self._lit_scores[node.var])
                    self._priority_queue.add(node.var + self._num_vars, self._lit_scores[node.var + self._num_vars])

                del node
                itr -= 1

        if node_to_add:
            self._nodes_variable[node_to_add.var] = node_to_add
            self._stack_of_decision.append(node_to_add)
            node_to_add.index = len(self._stack_of_decision) - 1

            if self._decider == "VSIDS":
                self._priority_queue.remove(node_to_add.var)
                self._priority_queue.remove(node_to_add.var + self._num_vars)

            self.stats._num_implications += 1

    def solve(self, cnf_filename):
        self.stats._input_file = cnf_filename
        self.stats._start_time = time.time()
        self._read_file(cnf_filename)
        self.stats._read_time = time.time()

        self.stats._num_vars = self._num_vars
        self.stats._num_clauses = self._num_clauses
        if self.stats._result == "UNSAT":
            self.stats._complete_time = time.time()
        else:
            first_time = True
            while True:
                while True:
                    result = self._unit_propagate(first_time)

                    if result == "NO_CONFLICT":
                        break
                    first_time = False

                    backtrack_level, node_to_add = self._analyze_conflict()

                    if backtrack_level == -1:
                        print("UNSAT")
                        self.stats._result = "UNSAT"
                        self.stats._complete_time = time.time()
                        break

                    self._backtrack(backtrack_level, node_to_add)

                if self.stats._result == "UNSAT":
                    break
                first_time = False
                var_decided = self._decide()

                if var_decided == -1:
                    print("SAT")
                    self.stats._result = "SAT"
                    self.stats._complete_time = time.time()
                    break

        if not os.path.isdir("results"):
            os.mkdir("results")
        inputfile_basename = os.path.basename(cnf_filename)
        input_case_name = os.path.splitext(inputfile_basename)[0]
        self.stats.print_stats()

        if self.stats._result == "SAT":
            assgn_file_name = "results/decision_" + input_case_name + ".txt"
            self.stats._output_assignment_file = assgn_file_name

            assignment_dict = {}
            for var in self._nodes_variable:
                assignment_dict[var] = self._nodes_variable[var].value

            assgn_file = open(assgn_file_name, "w")
            assgn_file.write(json.dumps(assignment_dict))
            assgn_file.close()
