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

from functools import partial
from six import iteritems

from pysmt.exceptions import (NoSolverAvailableError, SolverRedefinitionError,
                              NoLogicAvailableError)
from pysmt.logics import QF_UFLIRA, LRA, QF_UFLRA
from pysmt.logics import AUTO as AUTO_LOGIC
from pysmt.logics import most_generic_logic, get_closer_logic
from pysmt.oracles import get_logic

DEFAULT_SOLVER_PREFERENCE_LIST = ['msat', 'z3', 'cvc4', 'yices', 'picosat', 'bdd']
DEFAULT_QELIM_PREFERENCE_LIST = ['z3', 'msat_fm', 'msat_lw']
DEFAULT_INTERPOLATION_PREFERENCE_LIST = ['msat', 'z3']
DEFAULT_LOGIC = QF_UFLIRA
DEFAULT_QE_LOGIC = LRA
DEFAULT_INTERPOLATION_LOGIC = QF_UFLRA

class Factory(object):

    def __init__(self, environment,
                 solver_preference_list=None,
                 qelim_preference_list=None,
                 interpolation_preference_list=None):
        self.environment = environment
        self._all_solvers = None
        self._all_unsat_core_solvers = None
        self._all_qelims = None
        self._all_interpolators = None
        self._generic_solvers = {}

        if solver_preference_list is None:
            solver_preference_list = DEFAULT_SOLVER_PREFERENCE_LIST
        self.solver_preference_list = solver_preference_list

        if qelim_preference_list is None:
            qelim_preference_list = DEFAULT_QELIM_PREFERENCE_LIST

        if interpolation_preference_list is None:
            interpolation_preference_list = \
                                          DEFAULT_INTERPOLATION_PREFERENCE_LIST
        self.qelim_preference_list = qelim_preference_list
        self.interpolation_preference_list = interpolation_preference_list
        self._default_logic = DEFAULT_LOGIC
        self._default_qe_logic = DEFAULT_QE_LOGIC
        self._default_interpolation_logic = DEFAULT_INTERPOLATION_LOGIC

        self._get_available_solvers()
        self._get_available_qe()
        self._get_available_interpolators()


    def get_solver(self, quantified=False, name=None, logic=None):
        assert quantified is False or logic is None, \
            "Cannot specify both quantified and logic."

        if quantified is True:
            logic = self.default_logic.get_quantified_version

        SolverClass, closer_logic = \
           self._get_solver_class(solver_list=self._all_solvers,
                                  solver_type="Solver",
                                  preference_list=self.solver_preference_list,
                                  default_logic=self.default_logic,
                                  name=name,
                                  logic=logic)

        return SolverClass(environment=self.environment,
                           logic=closer_logic,
                           user_options={"generate_models" : True})


    def get_unsat_core_solver(self, quantified=False, name=None,
                              logic=None, unsat_cores_mode="all"):
        assert quantified is False or logic is None, \
            "Cannot specify both quantified and logic."

        if quantified is True:
            logic = self.default_logic.get_quantified_version

        SolverClass, closer_logic = \
           self._get_solver_class(solver_list=self._all_unsat_core_solvers,
                                  solver_type="Solver supporting Unsat Cores",
                                  preference_list=self.solver_preference_list,
                                  default_logic=self.default_logic,
                                  name=name,
                                  logic=logic)

        return SolverClass(environment=self.environment,
                           logic=closer_logic,
                           user_options={"generate_models" : True,
                                         "unsat_cores_mode" : unsat_cores_mode})


    def get_quantifier_eliminator(self, name=None, logic=None):
        SolverClass, closer_logic = \
           self._get_solver_class(solver_list=self._all_qelims,
                                  solver_type="Quantifier Eliminator",
                                  preference_list=self.qelim_preference_list,
                                  default_logic=self.default_qe_logic,
                                  name=name,
                                  logic=logic)

        return SolverClass(environment=self.environment,
                           logic=closer_logic)

    def get_interpolator(self, name=None, logic=None):
        SolverClass, closer_logic = self._get_solver_class(
            solver_list=self._all_interpolators,
            solver_type="Interpolator",
            preference_list=self.interpolation_preference_list,
            default_logic=self._default_interpolation_logic,
            name=name,
            logic=logic)

        return SolverClass(environment=self.environment,
                           logic=closer_logic)


    def _get_solver_class(self, solver_list, solver_type, preference_list,
                          default_logic, name=None, logic=None):
        if len(solver_list) == 0:
            raise NoSolverAvailableError("No %s is available" % solver_type)

        if name is not None:
            if name not in solver_list:
                raise NoSolverAvailableError("%s '%s' is not available" % \
                                             (solver_type, name))

            if logic is not None and \
               name not in self._filter_solvers(solver_list, logic=logic):
                raise NoSolverAvailableError("%s '%s' does not support logic %s"%
                                             (solver_type, name, logic))

            SolverClass = solver_list[name]
            if logic is None:
                try:
                    logic = most_generic_logic(SolverClass.LOGICS)
                except NoLogicAvailableError:
                    if default_logic in SolverClass.LOGICS:
                        logic = default_logic
                    else:
                        raise NoLogicAvailableError("Cannot automatically select a logic")

            closer_logic = get_closer_logic(SolverClass.LOGICS, logic)

            return SolverClass, closer_logic

        if logic is None:
            logic = default_logic

        solvers = self._filter_solvers(solver_list, logic=logic)

        if solvers is not None and len(solvers) > 0:
            # Pick the first solver based on preference list
            SolverClass = self._pick_favorite(preference_list, solver_list, solvers)
            closer_logic = get_closer_logic(SolverClass.LOGICS, logic)
            return SolverClass, closer_logic

        else:
            raise NoSolverAvailableError("No %s is available for logic %s" %
                                         (solver_type, logic))


    def _pick_favorite(self, preference_list, solver_list, solvers):
        for candidate in preference_list:
            if candidate in solvers:
                return solver_list[candidate]
        raise NoSolverAvailableError(
            "Cannot find a matching solver in the preference list: %s " % solvers)


    def add_generic_solver(self, name, args, logics, unsat_core_support=False):
        from pysmt.smtlib.solver import SmtLibSolver
        if name in self._all_solvers:
            raise SolverRedefinitionError("Solver %s already defined" % name)
        self._generic_solvers[name] = (args, logics)
        solver = partial(SmtLibSolver, args)
        solver.LOGICS = logics
        solver.UNSAT_CORE_SUPPORT = unsat_core_support
        self._all_solvers[name] = solver

    def is_generic_solver(self, name):
        return name in self._generic_solvers

    def get_generic_solver_info(self, name):
        return self._generic_solvers[name]

    def _get_available_solvers(self):
        self._all_solvers = {}
        self._all_unsat_core_solvers = {}

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


        try:
            from pysmt.solvers.pico import PicosatSolver
            self._all_solvers['picosat'] = PicosatSolver

        except ImportError:
            pass


        for k,s in iteritems(self._all_solvers):
            try:
                if s.UNSAT_CORE_SUPPORT:
                    self._all_unsat_core_solvers[k] = s
            except AttributeError:
                pass


    def _get_available_qe(self):
        self._all_qelims = {}

        try:
            from pysmt.solvers.z3 import Z3QuantifierEliminator
            self._all_qelims['z3'] = Z3QuantifierEliminator
        except ImportError:
            pass

        try:
            from pysmt.solvers.msat import (MSatFMQuantifierEliminator,
                                            MSatLWQuantifierEliminator)
            self._all_qelims['msat_fm'] = MSatFMQuantifierEliminator
            self._all_qelims['msat_lw'] = MSatLWQuantifierEliminator
        except ImportError:
            pass

        try:
            from pysmt.solvers.bdd import BddQuantifierEliminator
            self._all_qelims['bdd'] = BddQuantifierEliminator
        except ImportError:
            pass


    def _get_available_interpolators(self):
        self._all_interpolators = {}

        try:
            from pysmt.solvers.z3 import Z3Interpolator
            self._all_interpolators['z3'] = Z3Interpolator
        except ImportError:
            pass

        try:
            from pysmt.solvers.msat import MSatInterpolator
            self._all_interpolators['msat'] = MSatInterpolator
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


    def set_interpolation_preference_list(self, preference_list):
        """Defines the order in which to pick the solvers."""
        assert preference_list is not None
        assert len(preference_list) > 0
        self.interpolation_preference_list = preference_list
        

    def _filter_solvers(self, solver_list, logic=None):
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
            for s, v in iteritems(solver_list):
                for l in v.LOGICS:
                    if logic <= l:
                        res[s] = v
                        break
            return res
        else:
            solvers = solver_list

        return solvers


    def all_solvers(self, logic=None):
        """
        Returns a dict <solver_name, solver_class> including all and only
        the solvers directly or indirectly supporting the given logic.
        A solver supports a logic if either the given logic is
        declared in the LOGICS class field or if a logic subsuming the
        given logic is declared in the LOGICS class field.

        If logic is None, the map will contain all the known solvers
        """
        return self._filter_solvers(self._all_solvers, logic=logic)


    def all_quantifier_eliminators(self, logic=None):
        """Returns a dict <qelim_name, qelim_class> including all and only the
        quantifier eliminators directly or indirectly supporting the
        given logic.  A qelim supports a logic if either the given
        logic is declared in the LOGICS class field or if a logic
        subsuming the given logic is declared in the LOGICS class
        field.

        If logic is None, the map will contain all the known
        quantifier eliminators
        """
        return self._filter_solvers(self._all_qelims, logic=logic)


    def all_unsat_core_solvers(self, logic=None):
        """
        Returns a dict <solver_name, solver_class> including all and only
        the solvers supporting unsat core extraction and directly or
        indirectly supporting the given logic.  A solver supports a
        logic if either the given logic is declared in the LOGICS
        class field or if a logic subsuming the given logic is
        declared in the LOGICS class field.

        If logic is None, the map will contain all the known solvers
        """
        return self._filter_solvers(self._all_unsat_core_solvers, logic=logic)



    ##
    ## Wrappers: These functions are exported in shortcuts
    ##
    def Solver(self, quantified=False, name=None, logic=None):
        return self.get_solver(quantified=quantified,
                               name=name,
                               logic=logic)

    def UnsatCoreSolver(self, quantified=False, name=None, logic=None,
                        unsat_cores_mode="all"):
        return self.get_unsat_core_solver(quantified=quantified,
                                          name=name,
                                          logic=logic,
                                          unsat_cores_mode=unsat_cores_mode)


    def QuantifierEliminator(self, name=None, logic=None):
        return self.get_quantifier_eliminator(name=name, logic=logic)

    def Interpolator(self, name=None, logic=None):
        return self.get_interpolator(name=name, logic=logic)

    def is_sat(self, formula, solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(formula, self.environment)
        with self.Solver(name=solver_name, logic=logic) \
             as solver:
            return solver.is_sat(formula)

    def get_model(self, formula, solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(formula, self.environment)
        with self.Solver(name=solver_name, logic=logic) \
             as solver:
            solver.add_assertion(formula)
            check = solver.solve()
            retval = None
            if check:
                retval = solver.get_model()
            return retval

    def get_unsat_core(self, clauses, solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(self.environment.formula_manager.And(clauses),
                              self.environment)

        with self.UnsatCoreSolver(name=solver_name, logic=logic) \
             as solver:
            for c in clauses:
                solver.add_assertion(c)
            check = solver.solve()
            if check:
                return None

            return solver.get_unsat_core()

    def is_valid(self, formula, solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(formula, self.environment)
        with self.Solver(name=solver_name, logic=logic) \
             as solver:
            return solver.is_valid(formula)

    def is_unsat(self, formula, solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(formula, self.environment)
        with self.Solver(name=solver_name, logic=logic) \
             as solver:
            return solver.is_unsat(formula)

    def qelim(self, formula, solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(formula, self.environment)

        with self.QuantifierEliminator(name=solver_name, logic=logic) as qe:
            return qe.eliminate_quantifiers(formula)


    def binary_interpolant(self, formula_a, formula_b,
                           solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(
                self.environment.formula_manager.And(formula_a, formula_b))

        with self.Interpolator(name=solver_name, logic=logic) as itp:
            return itp.binary_interpolant(formula_a, formula_b)


    def sequence_interpolant(self, formulas, solver_name=None, logic=None):
        if logic == AUTO_LOGIC:
            logic = get_logic(
                self.environment.formula_manager.And(formulas))

        with self.Interpolator(name=solver_name, logic=logic) as itp:
            return itp.sequence_interpolant(formulas)
        

    @property
    def default_logic(self):
        return self._default_logic

    @default_logic.setter
    def default_logic(self, value):
        self._default_logic = value

    @property
    def default_qe_logic(self):
        return self._default_qe_logic

    @default_qe_logic.setter
    def default_qe_logic(self, value):
        self._default_qe_logic = value
