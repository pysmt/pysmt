#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
from six.moves import xrange

from pysmt.exceptions import SolverAPINotFound

try:
    import repycudd
except ImportError:
    raise SolverAPINotFound

import pysmt.logics
from pysmt import typing as types
from pysmt.solvers.solver import Solver, Converter, SolverOptions
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.oracles import get_logic
from pysmt.solvers.qelim import QuantifierEliminator


class BddOptions(SolverOptions):
    ## CUDD Reordering algorithms
    CUDD_REORDER_SAME, \
    CUDD_REORDER_NONE, \
    CUDD_REORDER_RANDOM, \
    CUDD_REORDER_RANDOM_PIVOT, \
    CUDD_REORDER_SIFT, \
    CUDD_REORDER_SIFT_CONVERGE, \
    CUDD_REORDER_SYMM_SIFT, \
    CUDD_REORDER_SYMM_SIFT_CONV, \
    CUDD_REORDER_WINDOW2, \
    CUDD_REORDER_WINDOW3, \
    CUDD_REORDER_WINDOW4, \
    CUDD_REORDER_WINDOW2_CONV, \
    CUDD_REORDER_WINDOW3_CONV, \
    CUDD_REORDER_WINDOW4_CONV, \
    CUDD_REORDER_GROUP_SIFT, \
    CUDD_REORDER_GROUP_SIFT_CONV, \
    CUDD_REORDER_ANNEALING, \
    CUDD_REORDER_GENETIC, \
    CUDD_REORDER_LINEAR, \
    CUDD_REORDER_LINEAR_CONVERGE, \
    CUDD_REORDER_LAZY_SIFT, \
    CUDD_REORDER_EXACT = range(22)

    CUDD_ALL_REORDERING_ALGORITHMS = range(1, 22)

    VALID_OPTIONS = SolverOptions.VALID_OPTIONS + \
                    [("static_ordering", None),
                     ("dynamic_reordering", False),
                     ("reordering_algorithm", CUDD_REORDER_SIFT),
                    ]

    def __init__(self, **kwargs):
        SolverOptions.__init__(self, **kwargs)

        if self.unsat_cores_mode is not None:
            # Check if, for some reason, unsat cores are
            # required. In case, raise an error.
            #
            # TODO: This should be within the Solver, here we should
            # only check that options are set and non-contraddicting.
            #
            raise NotImplementedError("BddSolver does not "\
                                      "support unsat cores")

    # @classmethod
    # def from_base_options(cls, base_options):
    #     generate_models=base_options.generate_models
    #     unsat_cores_mode=base_options.unsat_cores_mode
    #     incremental=base_options.incremental
    #     return BddOptions(generate_models=generate_models,
    #                       unsat_cores_mode=unsat_cores_mode,
    #                       incremental=incremental)



class BddSolver(Solver):
    LOGICS = [ pysmt.logics.QF_BOOL, pysmt.logics.BOOL ]

    OptionsClass = BddOptions

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)

        self.mgr = environment.formula_manager
        self.ddmanager = repycudd.DdManager()
        self.converter = BddConverter(environment=self.environment,
                                      ddmanager=self.ddmanager)

        # Impose initial ordering
        if self.options.static_ordering is not None:
            for var in self.options.static_ordering:
                if not var.is_symbol(types.BOOL):
                    raise ValueError("The BDD static ordering must be a " \
                                     "list of Boolean variables")
                self.declare_variable(var)

        if self.options.dynamic_reordering:
            self.ddmanager.AutodynEnable(self.options.reordering_algorithm)
        else:
            self.ddmanager.AutodynDisable()

        # This stack keeps a pair (Expr, Bdd), with the semantics that
        # the bdd at the i-th element of the list contains the bdd of
        # the conjunction of all previous expressions.
        # The construction of the Bdd is done during solve()
        self.assertions_stack = None
        self.reset_assertions() # Initialize the stack

        self.backtrack = []
        self.latest_model = None

    @clear_pending_pop
    def reset_assertions(self):
        true_formula = self.mgr.Bool(True)
        self.assertions_stack = [(true_formula,
                                  self.converter.convert(true_formula))]

    @clear_pending_pop
    def declare_variable(self, var):
        self.converter.declare_variable(var)

    @clear_pending_pop
    def add_assertion(self, formula, named=None):
        self.assertions_stack.append((formula, None))

    @clear_pending_pop
    def solve(self, assumptions=None):
        if assumptions is not None:
            self.push()
            self.add_assertion(self.mgr.And(assumptions))
            self.pending_pop = True

        for (i, (expr, bdd)) in enumerate(self.assertions_stack):
            if bdd is None:
                bdd_expr = self.converter.convert(expr)
                _, previous_bdd = self.assertions_stack[i-1]
                new_bdd = self.ddmanager.And(previous_bdd, bdd_expr)
                self.assertions_stack[i] = (expr, new_bdd)

        _, current_state = self.assertions_stack[-1]
        res = (current_state != self.ddmanager.Zero())
        # Invalidate cached model
        self.latest_model = None
        return res


    def get_value(self, item):
        if self.latest_model is None:
            self.get_model()
        return self.latest_model.get_value(item)

    def get_model(self):
        # TODO: We could provide a more sophisticated Model class,
        # that would contain the current Bdd and a copy of the
        # DdManager. This would make it possible to apply other
        # operations on the model (e.g., enumeration) in a simple way.
        if self.latest_model is None:
            _, current_state = self.assertions_stack[-1]
            assert current_state is not None, "solve() should be called before get_model()"
            # Build ddArray of variables
            var_array = self.converter.get_all_vars_array()
            minterm_set = self.ddmanager.PickOneMinterm(current_state,
                                                        var_array,
                                                        len(var_array))
            minterm = next(repycudd.ForeachCubeIterator(self.ddmanager,
                                                        minterm_set))
            assignment = {}
            for i, node in enumerate(var_array):
                value = self.mgr.Bool(minterm[i] == 1)
                key = self.converter.idx2var[node.NodeReadIndex()]
                assignment[key] = value

            self.latest_model = EagerModel(assignment=assignment,
                                           environment=self.environment)
        return self.latest_model

    @clear_pending_pop
    def push(self, levels=1):
        for _ in xrange(levels):
            self.backtrack.append(len(self.assertions_stack))

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in xrange(levels):
            l = self.backtrack.pop()
            self.assertions_stack = self.assertions_stack[:l]

    def _exit(self):
        del self.ddmanager


class BddConverter(Converter, DagWalker):

    def __init__(self, environment, ddmanager):
        DagWalker.__init__(self)

        self.environment = environment
        self.fmgr = self.environment.formula_manager
        self.ddmanager = ddmanager
        # Note: Nodes in repycudd are not shared, but they overload all
        # methods to perform comparison. This means that for two
        # wrappers for the variable x, we have that id(x) != id(x1)
        # but x == x1.  Nevertheless, we need to store the ids, since
        # nodes can be moved during operations by the
        # ddManager. Therefore, when using nodes in a map, we should
        # use the ids.
        self.idx2var = {}
        self.var2node = {}
        self.back_memoization = {}

    @catch_conversion_error
    def convert(self, formula):
        """Convert a PySMT formula into a BDD."""
        return self.walk(formula)

    def back(self, bdd_expr):
        return self._walk_back(bdd_expr, self.fmgr).simplify()

    def get_all_vars_array(self):
        # NOTE: This way of building the var_array does not look
        #       robust.  There might be an issue if variables are
        #       added and the order of enumeration of the dictionary
        #       changes and we rely on this order outside of this class.
        var_array = repycudd.DdArray(self.ddmanager, len(self.idx2var))
        for i, node_idx in enumerate(self.idx2var):
            var_array[i] = self.ddmanager[node_idx]
        return var_array

    def cube_from_var_list(self, var_list):
        indices = repycudd.IntArray(len(var_list))
        for i, v in enumerate(var_list):
            indices[i] = self.var2node[v].NodeReadIndex()
        cube = self.ddmanager.IndicesToCube(indices, len(var_list))
        return cube

    def declare_variable(self, var):
        if not var.is_symbol(type_=types.BOOL): raise TypeError
        if var not in self.var2node:
            node = self.ddmanager.NewVar()
            self.idx2var[node.NodeReadIndex()] = var
            self.var2node[var] = node

    def walk_and(self, formula, args, **kwargs):
        res = args[0]
        for a in args[1:]:
            res = self.ddmanager.And(a, res)
        return res

    def walk_or(self, formula, args, **kwargs):
        res = args[0]
        for a in args[1:]:
            res = self.ddmanager.Or(res,a)
        return res

    def walk_not(self, formula, args, **kwargs):
        return self.ddmanager.Not(args[0])

    def walk_symbol(self, formula, **kwargs):
        if not formula.is_symbol(types.BOOL): raise TypeError
        if formula not in self.var2node:
            self.declare_variable(formula)
        res = self.var2node[formula]
        return res

    def walk_implies(self, formula, args, **kwargs):
        lhs, rhs = args
        return self.ddmanager.Or(lhs.Not(), rhs)

    def walk_iff(self, formula, args, **kwargs):
        lhs, rhs = args
        pos = self.ddmanager.And(lhs, rhs)
        neg = self.ddmanager.And(lhs.Not(), rhs.Not())
        return self.ddmanager.Or(pos, neg)

    def walk_forall(self, formula, args, **kwargs):
        f = args[0]
        cube = self.cube_from_var_list(formula.quantifier_vars())
        res = self.ddmanager.UnivAbstract(f, cube)
        return res

    def walk_exists(self, formula, args, **kwargs):
        f = args[0]
        cube = self.cube_from_var_list(formula.quantifier_vars())
        res = self.ddmanager.ExistAbstract(f, cube)
        return res

    def walk_bool_constant(self, formula, **kwargs):
        if formula.is_true():
            return self.ddmanager.One()
        else:
            return self.ddmanager.Zero()


    def _walk_back(self, bdd, mgr):
        stack = [bdd]
        while len(stack) > 0:
            current = stack.pop()
            # If the node haven't been explored yet, it is not in back_memoization,
            # If back_memoization contains None, we are exploring the children
            # Otherwise, it contains the pySMT expression corresponding to the node
            if current not in self.back_memoization:
                self.back_memoization[current] = None
                stack.append(current)
                if current != self.ddmanager.Zero() and \
                   current != self.ddmanager.One():
                    t = current.T()
                    e = current.E()
                    stack.append(t)
                    stack.append(e)
            elif self.back_memoization[current] is None:
                if current == self.ddmanager.Zero():
                    res = mgr.FALSE()
                elif current == self.ddmanager.One():
                    res = mgr.TRUE()
                else:
                    var = self.idx2var[current.NodeReadIndex()]
                    t = current.T()
                    e = current.E()
                    expr_t = self.back_memoization[t]
                    expr_e = self.back_memoization[e]

                    if current.IsComplement():
                        # (v /\ !t) \/ (!v /\ !e)
                        #     P            N
                        p = mgr.And(var, mgr.Not(expr_t))
                        n = mgr.And(mgr.Not(var), mgr.Not(expr_e))
                        res = mgr.Or(p, n)
                    else:
                        # (v /\ t) \/ (!v /\ e)
                        #    P             N
                        p = mgr.And(var, expr_t)
                        n = mgr.And(mgr.Not(var), expr_e)
                        res = mgr.Or(p, n)

                self.back_memoization[current] = res
            else:
                # we already visited the node, nothing else to do
                pass
        return self.back_memoization[bdd]

# EOC BddConverter


class BddQuantifierEliminator(QuantifierEliminator):

    LOGICS = [pysmt.logics.BOOL]

    def __init__(self, environment, logic=None):
        QuantifierEliminator.__init__(self)
        self.environment = environment
        self.logic = logic
        self.ddmanager = repycudd.DdManager()
        self.converter = BddConverter(environment=environment,
                                      ddmanager=self.ddmanager)

    def eliminate_quantifiers(self, formula):
        logic = get_logic(formula, self.environment)
        if not logic <= pysmt.logics.BOOL:
            raise NotImplementedError("BDD-based quantifier elimination only "\
                                      "supports pure-boolean formulae."\
                                      "(detected logic is: %s)" % str(logic))

        bdd = self.converter.convert(formula)
        pysmt_res = self.converter.back(bdd)
        return pysmt_res

    def _exit(self):
        del self.ddmanager
