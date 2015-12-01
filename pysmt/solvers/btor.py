#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
from math import log, ceil

from pysmt.exceptions import SolverAPINotFound

try:
    import boolector
except ImportError:
    raise SolverAPINotFound


from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              ConvertExpressionError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.logics import QF_BV, QF_UFBV
from pysmt.oracles import get_logic



class BoolectorSolver(IncrementalTrackingSolver,
                      SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = [QF_BV, QF_UFBV]

    def __init__(self, environment, logic, user_options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           user_options=user_options)

        self.btor = boolector.Boolector()
        self.btor.Set_opt("incremental", 1)
        self.btor.Set_opt("model_gen", 1)
        self.converter = BTORConverter(environment, self.btor)
        self.mgr = environment.formula_manager
        self.declarations = {}
        return

    @clear_pending_pop
    def _reset_assertions(self):
        raise NotImplementedError

    @clear_pending_pop
    def declare_variable(self, var):
        raise NotImplementedError

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.btor.Assert(term)

    def get_model(self):
        assignment = {}
        for s, _ in self.converter.declared_vars.items():
            assignment[s] = self.get_value(s)
        return EagerModel(assignment=assignment, environment=self.environment)

    @clear_pending_pop
    def _solve(self, assumptions=None):
        if assumptions is not None:
            assumption = self.mgr.And(assumptions)
            self._assert_is_boolean(assumption)
            btor_assumption =  self.converter.convert(assumption)
            self.btor.Assume(btor_assumption)

        res = self.btor.Sat()
        if res == self.btor.SAT:
            return True
        elif res == self.btor.UNSAT:
            return False
        else:
            raise SolverReturnedUnknownResultError

    def get_unsat_core(self):
        raise NotImplementedError

    @clear_pending_pop
    def _push(self, levels=1):
        # Boolector does not support push/pop.
        # Incrementality could be simulated by keeping a stack
        # of boolector instances.
        # See self.btor.Clone()
        raise NotImplementedError

    @clear_pending_pop
    def _pop(self, levels=1):
        raise NotImplementedError

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print("%s = %s" % (var.symbol_name(), self.get_value(var)))

    def get_value(self, item):
        self._assert_no_function_type(item)
        titem = self.converter.convert(item)
        if item.is_symbol() and item.symbol_type().is_bv_type():
            return self.mgr.BV(titem.assignment, item.bv_width())
        else:
            return self.mgr.Bool(bool(int(titem.assignment)))

    def _exit(self):
        del self.btor


class BTORConverter(Converter, DagWalker):

    def __init__(self, environment, btor):
        DagWalker.__init__(self, environment)
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type
        self._back_memoization = {}
        self._btor = btor
        self.declared_vars = {}
        self.function_declarations = {}
        return

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def back(self, expr):
        raise NotImplementedError

    def declare_function(self, formula):
        name = formula.function_name()
        if name not in self.function_declarations:
            tp = self._type_to_btor(name.symbol_type())
            decl = self._btor.UF(tp)
            self.function_declarations[name] = decl
        else:
            decl = self.function_declarations[name]
        return decl

    def walk_and(self, formula, args, **kwargs):
        #pylint: disable=star-args
        assert len(args) >= 2
        res = self._btor.And(args[0], args[1])
        for conj in args[2:]:
            res = self._btor.And(res, conj)
        return res

    def walk_or(self, formula, args, **kwargs):
        #pylint: disable=star-args
        assert len(args) >= 2
        res = self._btor.Or(args[0], args[1])
        for disj in args[2:]:
            res = self._btor.Or(res, disj)
        return res

    def walk_not(self, formula, args, **kwargs):
        return self._btor.Not(args[0])

    def walk_symbol(self, formula, **kwargs):
        symbol_type = formula.symbol_type()
        if symbol_type.is_bool_type():
            res = self._btor.Var(1, formula.symbol_name())
        elif symbol_type.is_real_type():
            raise ConvertExpressionError
        elif symbol_type.is_int_type():
            raise ConvertExpressionError
        else:
            assert symbol_type.is_bv_type()
            res = self._btor.Var(formula.bv_width(),
                                 formula.symbol_name())
        self.declared_vars[formula] = res
        return res

    def walk_iff(self, formula, args, **kwargs):
        return self._btor.Iff(*args)

    def walk_implies(self, formula, args, **kwargs):
        return self._btor.Implies(*args)

    def walk_ite(self, formula, args, **kwargs):
        return self._btor.Cond(*args)

    def walk_bool_constant(self, formula, **kwargs):
        return self._btor.Const(formula.constant_value())

    def walk_equals(self, formula, args, **kwargs):
        return self._btor.Eq(*args)

    def walk_function(self, formula, args, **kwargs):
        #pylint: disable=star-args
        _uf = self.declare_function(formula)
        return _uf(*args)

    def walk_bv_constant(self, formula, **kwargs):
        value = formula.constant_value()
        width = formula.bv_width()
        return self._btor.Const(value, width)

    def walk_bv_ult(self, formula, args, **kwargs):
        return self._btor.Ult(args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return self._btor.Ulte(args[0], args[1])

    def walk_bv_concat(self, formula, args, **kwargs):
        return self._btor.Concat(args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        start = formula.bv_extract_start()
        end = formula.bv_extract_end()
        return self._btor.Slice(args[0], end, start)

    def walk_bv_or(self, formula, args, **kwargs):
        return self.walk_or(formula, args, **kwargs)

    def walk_bv_not(self, formula, args, **kwargs):
        return self.walk_not(formula, args, **kwargs)

    def walk_bv_and(self, formula, args, **kwargs):
        return self.walk_and(formula, args, **kwargs)

    def walk_bv_xor(self, formula, args, **kwargs):
        return self._btor.Xor(*args)

    def walk_bv_add(self, formula, args, **kwargs):
        return self._btor.Add(args[0], args[1])

    def walk_bv_sub(self, formula, args, **kwargs):
        return self._btor.Sub(args[0], args[1])

    def walk_bv_neg(self, formula, args, **kwargs):
        return -args[0]

    def walk_bv_mul(self, formula, args, **kwargs):
        return args[0]*args[1]

    def walk_bv_udiv(self, formula, args, **kwargs):
        return args[0] / args[1]

    def walk_bv_urem(self, formula, args, **kwargs):
        return self._btor.Urem(args[0], args[1])

    def walk_bv_lshl(self, formula, args, **kwargs):
        # Boolector requires that witdh(rhs) = log2(width(lhs))
        lhs_w = args[0].width
        rhs_w = args[1].width
        target_w = int(ceil(log(lhs_w, 2)))

        if rhs_w == target_w:
            return args[0] << args[1]
        else:
            # IF (rhs <= max) Then Rescale Else Max
            max_value = 2**target_w-1
            max_big = self._btor.Const(max_value, rhs_w)
            cond = self._btor.Ulte(args[1], max_big)
            max_small = self._btor.Const(max_value, target_w)
            rescaled = self._btor.Slice(args[1], target_w-1, 0)
            return args[0] << self._btor.Cond(cond,
                                              rescaled,
                                              max_small)

    def walk_bv_lshr(self, formula, args, **kwargs):
        # Boolector requires that witdh(rhs) = log2(width(lhs))
        lhs_w = args[0].width
        rhs_w = args[1].width
        target_w = int(ceil(log(lhs_w, 2)))

        if rhs_w == target_w:
            return args[0] >> args[1]
        else:
            # IF (rhs <= max) Then Rescale Else Max
            max_value = 2**target_w-1
            max_big = self._btor.Const(max_value, rhs_w)
            cond = self._btor.Ulte(args[1], max_big)
            max_small = self._btor.Const(max_value, target_w)
            rescaled = self._btor.Slice(args[1], target_w-1, 0)
            return args[0] >> self._btor.Cond(cond,
                                              rescaled,
                                              max_small)

    def walk_bv_rol(self, formula, args, **kwargs):
        return self._btor.Rol(args[0],
                             formula.bv_rotation_step())

    def walk_bv_ror(self, formula, args, **kwargs):
        return self._btor.Ror(args[0],
                             formula.bv_rotation_step())

    def walk_bv_zext(self, formula, args, **kwargs):
        return self._btor.Uext(args[0], formula.bv_extend_step())

    def walk_bv_sext (self, formula, args, **kwargs):
        return self._btor.Sext(args[0], formula.bv_extend_step())

    def walk_bv_slt(self, formula, args, **kwargs):
        return self._btor.Slt(args[0], args[1])

    def walk_bv_sle (self, formula, args, **kwargs):
        return self._btor.Slte(args[0], args[1])

    def walk_bv_comp (self, formula, args, **kwargs):
        return self._btor.Eq(args[0], args[1])

    def walk_bv_sdiv (self, formula, args, **kwargs):
        return self._btor.Sdiv(args[0], args[1])

    def walk_bv_srem (self, formula, args, **kwargs):
        return self._btor.Srem(args[0], args[1])

    def walk_bv_ashr (self, formula, args, **kwargs):
        # Boolector requires that witdh(rhs) = log2(width(lhs))
        lhs_w = args[0].width
        rhs_w = args[1].width
        target_w = int(ceil(log(lhs_w, 2)))

        if rhs_w == target_w:
            return self._btor.Sra(args[0], args[1])
        else:
            # IF (rhs <= max) Then Rescale Else Max
            max_value = 2**target_w-1
            max_big = self._btor.Const(max_value, rhs_w)
            cond = self._btor.Ulte(args[1], max_big)
            max_small = self._btor.Const(max_value, target_w)
            rescaled = self._btor.Slice(args[1], target_w-1, 0)
            return self._btor.Sra(args[0], self._btor.Cond(cond,
                                                           rescaled,
                                                           max_small))

    def _type_to_btor(self, tp):
        if tp.is_bool_type():
            return self._btor.BoolSort()
        elif tp.is_real_type():
            raise ConvertExpressionError
        elif tp.is_int_type():
            raise ConvertExpressionError
        elif tp.is_bv_type():
            return self._btor.BitVecSort(tp.width)
        else:
            assert tp.is_function_type() , "Unsupported type '%s'" % tp
            stps = [self._type_to_btor(x) for x in tp.param_types]
            rtp = self._type_to_btor(tp.return_type)
            return self._btor.FunSort(stps, rtp)
