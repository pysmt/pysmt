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
"""Factories are used to build new Solvers or Quantifier Eliminators
without the need of specifying them. For example, the user can simply
require a Solver that is able to deal with quantified theories, and
the factory will return one such solver among the available ones.
This makes it possible to write algorithms that do not depend on a
particular solver.
"""

import warnings
from functools import partial

from pysmt.exceptions import NoSolverAvailableError, SolverRedefinitionError
from pysmt.logics import PYSMT_LOGICS, most_generic_logic, get_closer_logic

DEFAULT_SOLVER_PREFERENCE_LIST = ['msat', 'z3', 'cvc4', 'yices', 'bdd']
DEFAULT_QELIM_PREFERENCE_LIST = ['z3']


class Factory(object):

    def __init__(self, environment,
                 solver_preference_list=None,
                 qelim_preference_list=None):
        self.environment = environment
        self._all_solvers = None
        self._all_qelims = None
        self._generic_solvers = {}

        if solver_preference_list is None:
            solver_preference_list = DEFAULT_SOLVER_PREFERENCE_LIST
        self.solver_preference_list = solver_preference_list

        if qelim_preference_list is None:
            qelim_preference_list = DEFAULT_QELIM_PREFERENCE_LIST
        self.qelim_preference_list = qelim_preference_list

        self._get_available_solvers()
        self._get_available_qe()


    def get_solver(self, quantified=False, name=None, logic=None):
        assert quantified is False or logic is None, \
            "Cannot specify both quantified and logic"

        if quantified is True:
            warnings.warn("Keyword 'quantified' in get_solver is deprecated" \
                          ", use 'logic=UFLIRA' instead",
                          DeprecationWarning)
            quantified = False
            logic = most_generic_logic(PYSMT_LOGICS)

        if name is not None:
            if name in self._all_solvers:
                if logic is None:
                    SolverClass = self._all_solvers[name]
                    logic = most_generic_logic(SolverClass.LOGICS)
                else:
                    if name in self.all_solvers(logic=logic):
                        SolverClass = self._all_solvers[name]
                    else:
                        raise NoSolverAvailableError("Solver '%s' does not" \
                                                     " support logic %s" %
                                                     (name, logic))

                closer_logic = get_closer_logic(SolverClass.LOGICS, logic)
                return SolverClass(environment=self.environment,
                                   logic=closer_logic,
                                   options=None)
            else:
                raise NoSolverAvailableError("Solver %s is not available" % name)

        if logic is None:
            logic = most_generic_logic(PYSMT_LOGICS)

        solvers = self.all_solvers(logic=logic)

        if solvers is not None and len(solvers) > 0:
            # Pick the first solver based on preference list
            SolverClass = self.pick_favorite_solver(solvers)
            closer_logic = get_closer_logic(SolverClass.LOGICS, logic)
            return SolverClass(environment=self.environment,
                               logic=closer_logic,
                               options=None)
        else:
            raise NoSolverAvailableError("No solver is available for logic %s" %\
                                         logic)



    def get_quantifier_eliminator(self, name=None):
        if len(self._all_qelims) == 0:
            raise NoSolverAvailableError("No quantifier eliminator is available")

        if name is None:
            QElimClass = self.pick_favorite_qelim(self._all_qelims)
        elif name in self._all_qelims:
            QElimClass = self._all_qelims[name]
        else:
            raise NoSolverAvailableError("No quantifier eliminator %s" % name)

        return QElimClass(self.environment)


    def pick_favorite_solver(self, solvers):
        for candidate in self.solver_preference_list:
            if candidate in solvers:
                return self._all_solvers[candidate]
        raise NoSolverAvailableError(
            "Cannot find a matching solver in the preference list: %s "% solvers)


    def pick_favorite_qelim(self, qelims):
        for candidate in self.qelim_preference_list:
            if candidate in qelims:
                return self._all_qelims[candidate]
        raise NoSolverAvailableError("Cannot find a matching quantifier " \
                                     "eliminator in the preference list")


    def add_generic_solver(self, name, args, logics):
        from pysmt.smtlib.solver import SmtLibSolver
        if name in self._all_solvers:
            raise SolverRedefinitionError("Solver %s already defined" % name)
        self._generic_solvers[name] = (args, logics)
        solver = partial(SmtLibSolver, args)
        solver.LOGICS = logics
        self._all_solvers[name] = solver

    def is_generic_solver(self, name):
        return name in self._generic_solvers

    def get_generic_solver_info(self, name):
        return self._generic_solvers[name]

    def _get_available_solvers(self):
        self._all_solvers = {}

        try:
            from pysmt.solvers.z3 import Z3Solver
            self._all_solvers['z3'] = Z3Solver

        except ImportError:
            pass

        try:
            from pysmt.solvers.msat import MathSAT5Solver
            self._all_solvers['msat'] = MathSAT5Solver

        except ImportError:
            pass

        try:
            from pysmt.solvers.cvc4 import CVC4Solver
            self._all_solvers['cvc4'] = CVC4Solver

        except ImportError:
            pass

        try:
            from pysmt.solvers.yices import YicesSolver
            self._all_solvers['yices'] = YicesSolver

        except ImportError:
            pass

        try:
            from pysmt.solvers.bdd import BddSolver
            self._all_solvers['bdd'] = BddSolver

        except ImportError:
            pass



    def _get_available_qe(self):
        self._all_qelims = {}

        try:
            from pysmt.solvers.z3 import Z3QuantifierEliminator
            self._all_qelims['z3'] = Z3QuantifierEliminator
        except ImportError:
            pass


    def set_solver_preference_list(self, preference_list):
        """Defines the order in which to pick the solvers.

        The list is not required to contain all the solvers. It is
        possible to define a subsets of the solvers, or even just
        one. The impact of this, is that the solver will never be
        selected automatically. Note, however, that the solver can
        still be selected by calling it by name.
        """
        assert preference_list is not None
        assert len(preference_list) > 0
        self.solver_preference_list = preference_list


    def set_qelim_preference_list(self, preference_list):
        """Defines the order in which to pick the solvers."""
        assert preference_list is not None
        assert len(preference_list) > 0
        self.qelim_preference_list = preference_list


    def all_solvers(self, logic=None):
        """
        Returns a dict <solver_name, solver_class> including all and only
        the solvers directly or indirectly supporting the given logic.
        A solver supports a logic if either the given logic is
        declared in the LOGICS class field or if a logic subsuming the
        given logic is declared in the LOGICS class field.

        If logic is None, the map will contain all the known solvers
        """
        res = {}
        if logic is not None:
            for s, v in self._all_solvers.iteritems():
                for l in v.LOGICS:
                    if logic <= l:
                        res[s] = v
                        break
            return res
        else:
            solvers = self._all_solvers

        return solvers

    def all_qelims(self):
        return self._all_qelims

    ##
    ## Wrappers: These functions are exported in shortcuts
    ##
    def Solver(self, quantified=False, name=None, logic=None):
        return self.get_solver(quantified=quantified,
                               name=name,
                               logic=logic)

    def QuantifierEliminator(self, name=None):
        return self.get_quantifier_eliminator(name=name)

    def is_sat(self, formula, quantified=None, solver_name=None, logic=None):
        solver = self.Solver(quantified=quantified, name=solver_name, logic=logic)
        return solver.is_sat(formula)

    def is_valid(self, formula, quantified=False, solver_name=None, logic=None):
        solver = self.Solver(quantified=quantified,
                             name=solver_name,
                             logic=logic)
        return solver.is_valid(formula)

    def is_unsat(self, formula, quantified=False, solver_name=None, logic=None):
        solver = self.Solver(quantified=quantified, name=solver_name, logic=logic)
        return solver.is_unsat(formula)

    def qelim(self, formula, solver_name=None):
        qe = self.QuantifierEliminator(name=solver_name)
        return qe.eliminate_quantifiers(formula)
