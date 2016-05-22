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
from pysmt.exceptions import SolverAPINotFound

try:
    import picosat
except ImportError:
    raise SolverAPINotFound

import pysmt.logics
from pysmt import typing as types
from pysmt.solvers.solver import Solver
from pysmt.solvers.eager import EagerModel
from pysmt.rewritings import CNFizer
from pysmt.decorators import clear_pending_pop, catch_conversion_error

from six.moves import xrange
from six import iteritems


class PicosatSolver(Solver):
    """PicoSAT solver"""

    LOGICS = [ pysmt.logics.QF_BOOL ]

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)

        self.mgr = environment.formula_manager
        self.pico = picosat.picosat_init()
        self.converter = None
        self.cnfizer = CNFizer(environment=environment)
        self.latest_model = None
        self._var_ids = {}


    def _get_var_id(self, symbol):
        if not symbol.is_symbol(types.BOOL):
            raise NotImplementedError("No theory terms are supported in PicoSAT")

        if symbol in self._var_ids:
            return self._var_ids[symbol]
        else:
            vid = picosat.picosat_inc_max_var(self.pico)
            self._var_ids[symbol] = vid
            return vid


    @clear_pending_pop
    def reset_assertions(self):
        picosat.picosat_reset(self.pico)
        self.pico = picosat.picosat_init()

    @clear_pending_pop
    def declare_variable(self, var):
        # no need to declare variables
        pass

    def _get_pico_lit(self, lit):
        mult = 1
        var = lit
        if lit.is_not():
            mult = -1
            var = lit.arg(0)

        vid = self._get_var_id(var)
        return vid * mult


    @clear_pending_pop
    @catch_conversion_error
    def add_assertion(self, formula, named=None):
        # First, we get rid of True/False constants
        formula = formula.simplify()
        if formula.is_false():
            picosat.picosat_add(self.pico, 0)
        elif not formula.is_true():
            cnf = self.cnfizer.convert(formula)
            self._add_cnf_assertion(cnf)

    def _add_cnf_assertion(self, cnf):
        for clause in cnf:
            for lit in clause:
                v = self._get_pico_lit(lit)
                picosat.picosat_add(self.pico, v)
            picosat.picosat_add(self.pico, 0)

    @clear_pending_pop
    @catch_conversion_error
    def solve(self, assumptions=None):
        if assumptions is not None:
            cnf = []
            for a in assumptions:
                cnf += self.cnfizer.convert(a)

            missing = []
            for clause in cnf:
                if len(clause) == 1:
                    v = self._get_pico_lit(next(iter(clause)))
                    picosat.picosat_assume(self.pico, v)
                else:
                    missing.append(clause)

            if len(missing) > 0:
                self.push()
                self._add_cnf_assertion(missing)
                self.pending_pop = True

        res = picosat.picosat_sat(self.pico, -1)
        if res == picosat.PICOSAT_SATISFIABLE:
            self.latest_model = self.get_model()
            return True
        else:
            self.latest_model = None
            return False


    def get_value(self, item):
        if self.latest_model is None:
            self.get_model()
        return self.latest_model.get_value(item)


    def get_model(self):
        assignment = {}
        for var, vid in iteritems(self._var_ids):
            v = picosat.picosat_deref(self.pico, vid)
            if v == 0:
                assert False

            value = self.mgr.Bool(v == 1)
            assignment[var] = value

        return EagerModel(assignment=assignment,
                          environment=self.environment)

    @clear_pending_pop
    def push(self, levels=1):
        for _ in xrange(levels):
            picosat.picosat_push(self.pico)

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in xrange(levels):
            picosat.picosat_pop(self.pico)

    def _exit(self):
        picosat.picosat_reset(self.pico)
