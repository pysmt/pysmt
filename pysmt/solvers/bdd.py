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
import warnings
from six.moves import xrange

import pycudd

import pysmt.logics

from pysmt import typing as types
from pysmt.solvers.solver import Solver, Converter
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.decorators import clear_pending_pop


class LockDdManager(object):
    """Context class that must be used to guard any usage of pycudd. This
    ensures that the default DdManager is the one passed at the
    constructor.

    E.g.

    with LockDdManager(ddmanager):
        Do something with bdds

    """
    _depth = 0

    def __init__(self, manager):
        self.manager = manager

    def __enter__(self):
        current_manager = pycudd.GetDefaultDdManager()
        assert current_manager is None or current_manager == self.manager
        self.manager.SetDefault()
        assert pycudd.GetDefaultDdManager() == self.manager
        LockDdManager._depth += 1

    def __exit__(self, type, value, traceback):
        if not pycudd.GetDefaultDdManager() == self.manager:
            warnings.warn("The default DdManager changed without a " \
                          "context protecting it")
        LockDdManager._depth -= 1
        if LockDdManager._depth == 0:
            pycudd.ResetDefaultDdManager()



class BddSolver(Solver):
    LOGICS = [ pysmt.logics.QF_BOOL, pysmt.logics.BOOL ]

    def __init__(self, environment, logic, user_options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        user_options=user_options)

        self.mgr = environment.formula_manager
        self.ddmanager = pycudd.DdManager()
        self.converter = BddConverter(environment=self.environment,
                                      ddmanager=self.ddmanager)

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
                with LockDdManager(self.ddmanager):
                    new_bdd = previous_bdd.And(bdd_expr)
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
            with LockDdManager(self.ddmanager):
                _, current_state = self.assertions_stack[-1]
                assert current_state is not None, "solve() should be called before get_model()"
                # Build ddArray of variables
                var_array = self.converter.get_all_vars_array()
                minterm_set = current_state.PickOneMinterm(var_array, len(var_array))
                minterm = next(iter(minterm_set))
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

    def exit(self):
        if not self._destroyed:
            self._destroyed = True
            del self.ddmanager


class BddConverter(Converter, DagWalker):

    def __init__(self, environment, ddmanager):
        DagWalker.__init__(self)

        self.environment = environment
        self.fmgr = self.environment.formula_manager
        self.ddmanager = ddmanager
        # Note: Nodes in pycudd are not shared, but they overload all
        # methods to perform comparison. This means that for two
        # wrappers for the variable x, we have that id(x) != id(x1)
        # but x == x1.  Nevertheless, we need to store the ids, since
        # nodes can be moved during operations by the
        # ddManager. Therefore, when using nodes in a map, we should
        # use the ids.
        self.idx2var = {}
        self.var2node = {}

    def convert(self, formula):
        """Convert a PySMT formula into a BDD."""
        with LockDdManager(self.ddmanager):
            return self.walk(formula)

    def back(self, bdd_expr):
        with LockDdManager(self.ddmanager):
            return self.bdd_to_expr3(bdd_expr).simplify()

    def get_all_vars_array(self):
        # NOTE: This way of building the var_array does not look
        #       robust.  There might be an issue if variables are
        #       added and the order of enumeration of the dictionary
        #       changes and we rely on this order outside of this class.
        with LockDdManager(self.ddmanager):
            var_array = pycudd.DdArray(len(self.idx2var))
            for i, node_idx in enumerate(self.idx2var):
                var_array[i] = self.ddmanager[node_idx]
            return var_array

    def cube_from_var_list(self, var_list):
        with LockDdManager(self.ddmanager):
            indices = pycudd.IntArray(len(var_list))
            for i, v in enumerate(var_list):
                indices[i] = self.var2node[v].NodeReadIndex()
            cube = self.ddmanager.IndicesToCube(indices, len(var_list))
            return cube

    def declare_variable(self, var):
        if not var.is_symbol(type_=types.BOOL): raise TypeError
        if var not in self.var2node:
            with LockDdManager(self.ddmanager):
                node = self.ddmanager.NewVar()
                self.idx2var[node.NodeReadIndex()] = var
                self.var2node[var] = node

    def walk_and(self, formula, args):
        res = args[0]
        for a in args[1:]:
            res = res.And(a)
        return res

    def walk_or(self, formula, args):
        res = args[0]
        for a in args[1:]:
            res = res.Or(a)
        return res

    def walk_not(self, formula, args):
        return args[0].Not()

    def walk_symbol(self, formula, args):
        if not formula.is_symbol(types.BOOL): raise TypeError
        if formula not in self.var2node:
            self.declare_variable(formula)
        res = self.var2node[formula]
        return res

    def walk_implies(self, formula, args):
        lhs, rhs = args
        return lhs.Not().Or(rhs)

    def walk_iff(self, formula, args):
        lhs, rhs = args
        # Double-check this
        pos = lhs.And(rhs)
        neg = lhs.Not().And(rhs.Not())
        return pos.Or(neg)

    def walk_forall(self, formula, args):
        f = args[0]
        cube = self.cube_from_var_list(formula.quantifier_vars())
        res = f.UnivAbstract(cube)
        return res

    def walk_exists(self, formula, args):
        f = args[0]
        cube = self.cube_from_var_list(formula.quantifier_vars())
        res = f.ExistAbstract(cube)
        return res

    def walk_bool_constant(self, formula, args):
        if formula.is_true():
            return self.ddmanager.One()
        else:
            return self.ddmanager.Zero()

    def bdd_to_expr(self, bdd):
        res = None
        if bdd == self.ddmanager.Zero():
            res = self.fmgr.Bool(False)
        elif bdd == self.ddmanager.One():
            res = self.fmgr.Bool(True)
        else:
            var = self.idx2var[bdd.NodeReadIndex()]
            t = self.fmgr.Implies(var, self.bdd_to_expr(bdd.T()))
            e = self.fmgr.Implies(self.fmgr.Not(var), self.bdd_to_expr(bdd.E()))
            # (v -> t) /\ (!v -> e)
            res = self.fmgr.And(t, e)

            if bdd.IsComplement():
                res = self.fmgr.Not(res)

        return res


    def bdd_to_expr2(self, bdd):
        res = None
        if bdd == self.ddmanager.Zero():
            res = self.fmgr.Bool(False)
        elif bdd == self.ddmanager.One():
            res = self.fmgr.Bool(True)
        else:
            var = self.idx2var[bdd.NodeReadIndex()]

            t = self.bdd_to_expr2(bdd.T())
            e = self.bdd_to_expr2(bdd.E())
            not_t = self.fmgr.Not(t)
            not_e = self.fmgr.Not(e)

            if bdd.IsComplement():
                # (v /\ !t) \/ (!v /\ !e)
                #     P            N
                p = self.fmgr.And(var, not_t)
                n = self.fmgr.And(self.fmgr.Not(var),
                                  not_e)
                res = self.fmgr.Or(p, n)
            else:
                # (v /\ t) \/ (!v /\ e)
                #    P             N
                p = self.fmgr.And(var, t)
                n = self.fmgr.And(self.fmgr.Not(var), e)
                res = self.fmgr.Or(p, n)

        return res


    def bdd_to_expr3(self, bdd, invert=False):
        """Convert a bdd into an expression and push negation."""

        res = None
        if bdd == self.ddmanager.Zero():
            res = self.fmgr.Bool(invert)
        elif bdd == self.ddmanager.One():
            res = self.fmgr.Bool(not invert)
        else:
            var = self.idx2var[bdd.NodeReadIndex()]

            if (bdd.IsComplement() and not invert) or \
               (not bdd.IsComplement() and invert):
                ne = self.bdd_to_expr3(bdd.E(), not invert)
                nt = self.bdd_to_expr3(bdd.T(), not invert)
                res = self.fmgr.Or(self.fmgr.And(var, nt),
                                   self.fmgr.And(self.fmgr.Not(var), ne))
            else:
                t = self.bdd_to_expr3(bdd.T(), invert)
                e = self.bdd_to_expr3(bdd.E(), invert)
                res = self.fmgr.Or(self.fmgr.And(var, t),
                                   self.fmgr.And(self.fmgr.Not(var), e))
        return res

 # EOC BddConverter
