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
    import pyboolector
except ImportError:
    raise SolverAPINotFound


from pysmt.solvers.solver import (IncrementalTrackingSolver,
                                  Converter, SolverOptions)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              ConvertExpressionError, PysmtValueError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.logics import QF_BV, QF_UFBV, QF_ABV, QF_AUFBV, QF_AX
from pysmt.constants import to_python_integer


class BoolectorOptions(SolverOptions):
    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        if self.random_seed is not None:
            raise PysmtValueError("BTOR Does not support Random Seed setting.")

        # Disabling Incremental usage is not allowed.
        # This needs to be set to 1
        self.incrementality = True
        self.internal_options = [pyboolector.BTOR_OPT_MODEL_GEN,
                                 pyboolector.BTOR_OPT_INCREMENTAL,
                                 pyboolector.BTOR_OPT_INCREMENTAL_SMT1,
                                 pyboolector.BTOR_OPT_INPUT_FORMAT,
                                 pyboolector.BTOR_OPT_OUTPUT_NUMBER_FORMAT,
                                 pyboolector.BTOR_OPT_OUTPUT_FORMAT,
                                 pyboolector.BTOR_OPT_ENGINE,
                                 pyboolector.BTOR_OPT_SAT_ENGINE,
                                 pyboolector.BTOR_OPT_AUTO_CLEANUP,
                                 pyboolector.BTOR_OPT_PRETTY_PRINT,
                                 pyboolector.BTOR_OPT_EXIT_CODES,
                                 pyboolector.BTOR_OPT_SEED,
                                 pyboolector.BTOR_OPT_VERBOSITY,
                                 pyboolector.BTOR_OPT_LOGLEVEL,
                                 pyboolector.BTOR_OPT_REWRITE_LEVEL,
                                 pyboolector.BTOR_OPT_SKELETON_PREPROC,
                                 pyboolector.BTOR_OPT_ACKERMANN,
                                 pyboolector.BTOR_OPT_BETA_REDUCE_ALL,
                                 pyboolector.BTOR_OPT_ELIMINATE_SLICES,
                                 pyboolector.BTOR_OPT_VAR_SUBST,
                                 pyboolector.BTOR_OPT_UCOPT,
                                 pyboolector.BTOR_OPT_MERGE_LAMBDAS,
                                 pyboolector.BTOR_OPT_EXTRACT_LAMBDAS,
                                 pyboolector.BTOR_OPT_NORMALIZE_ADD,
                                 pyboolector.BTOR_OPT_FUN_PREPROP,
                                 pyboolector.BTOR_OPT_FUN_PRESLS,
                                 pyboolector.BTOR_OPT_FUN_DUAL_PROP,
                                 pyboolector.BTOR_OPT_FUN_DUAL_PROP_QSORT,
                                 pyboolector.BTOR_OPT_FUN_JUST,
                                 pyboolector.BTOR_OPT_FUN_JUST_HEURISTIC,
                                 pyboolector.BTOR_OPT_FUN_LAZY_SYNTHESIZE,
                                 pyboolector.BTOR_OPT_FUN_EAGER_LEMMAS,
                                 pyboolector.BTOR_OPT_SLS_NFLIPS,
                                 pyboolector.BTOR_OPT_SLS_STRATEGY,
                                 pyboolector.BTOR_OPT_SLS_JUST,
                                 pyboolector.BTOR_OPT_SLS_MOVE_GW,
                                 pyboolector.BTOR_OPT_SLS_MOVE_RANGE,
                                 pyboolector.BTOR_OPT_SLS_MOVE_SEGMENT,
                                 pyboolector.BTOR_OPT_SLS_MOVE_RAND_WALK,
                                 pyboolector.BTOR_OPT_SLS_PROB_MOVE_RAND_WALK,
                                 pyboolector.BTOR_OPT_SLS_MOVE_RAND_ALL,
                                 pyboolector.BTOR_OPT_SLS_MOVE_RAND_RANGE,
                                 pyboolector.BTOR_OPT_SLS_MOVE_PROP,
                                 pyboolector.BTOR_OPT_SLS_MOVE_PROP_N_PROP,
                                 pyboolector.BTOR_OPT_SLS_MOVE_PROP_N_SLS,
                                 pyboolector.BTOR_OPT_SLS_MOVE_PROP_FORCE_RW,
                                 pyboolector.BTOR_OPT_SLS_MOVE_INC_MOVE_TEST,
                                 pyboolector.BTOR_OPT_SLS_USE_RESTARTS,
                                 pyboolector.BTOR_OPT_SLS_USE_BANDIT,
                                 pyboolector.BTOR_OPT_PROP_USE_RESTARTS,
                                 pyboolector.BTOR_OPT_PROP_USE_BANDIT,
                                 pyboolector.BTOR_OPT_PROP_PATH_SEL,
                                 pyboolector.BTOR_OPT_PROP_PROB_USE_INV_VALUE,
                                 pyboolector.BTOR_OPT_PROP_PROB_FLIP_COND,
                                 pyboolector.BTOR_OPT_PROP_PROB_FLIP_COND_CONST,
                                 pyboolector.BTOR_OPT_PROP_FLIP_COND_CONST_DELTA,
                                 pyboolector.BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
                                 pyboolector.BTOR_OPT_PROP_PROB_SLICE_KEEP_DC,
                                 pyboolector.BTOR_OPT_PROP_PROB_CONC_FLIP,
                                 pyboolector.BTOR_OPT_PROP_PROB_SLICE_FLIP,
                                 pyboolector.BTOR_OPT_PROP_PROB_EQ_FLIP,
                                 pyboolector.BTOR_OPT_PROP_PROB_AND_FLIP,
                                 pyboolector.BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT,
                                 pyboolector.BTOR_OPT_AIGPROP_USE_RESTARTS,
                                 pyboolector.BTOR_OPT_AIGPROP_USE_BANDIT,
                                 pyboolector.BTOR_OPT_SORT_EXP,
                                 pyboolector.BTOR_OPT_SORT_AIG,
                                 pyboolector.BTOR_OPT_SORT_AIGVEC,
                                 pyboolector.BTOR_OPT_AUTO_CLEANUP_INTERNAL,
                                 pyboolector.BTOR_OPT_SIMPLIFY_CONSTRAINTS,
                                 pyboolector.BTOR_OPT_CHK_FAILED_ASSUMPTIONS]


    def _set_option(self, btor, name, value):
        available_options = {pyboolector.BoolectorOpt(btor, io).lng : io
                             for io in self.internal_options}
        try:
            btor.Set_opt(available_options[name], value)
        except TypeError:
            raise PysmtValueError("Error setting the option '%s=%s'" \
                                  % (name,value))
        except pyboolector.BoolectorException:
            raise PysmtValueError("Error setting the option '%s=%s'" \
                                  % (name,value))
        except KeyError:
            raise PysmtValueError("Unable to set non-existing option '%s'. "
                                  "The accepted options options are: %s" \
                                  % (name, ", ".join(pyboolector.BoolectorOpt(btor, io).lng
                                                     for io in self.internal_options)))

    def __call__(self, solver):
        if self.generate_models:
            self._set_option(solver.btor, "model-gen", 1)
        else:
            self._set_option(solver.btor, "model-gen", 0)
        if self.incrementality:
            self._set_option(solver.btor, "incremental", 1)

        for k,v in self.solver_options.items():
            # Note: Options values in btor are mostly integers
            self._set_option(solver.btor, str(k), v)

# EOC BoolectorOptions


class BoolectorSolver(IncrementalTrackingSolver,
                      SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = [QF_BV, QF_UFBV, QF_ABV, QF_AUFBV, QF_AX]
    OptionsClass = BoolectorOptions

    def __init__(self, environment, logic, **options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           **options)
        self.btor = pyboolector.Boolector()
        self.options(self)
        self.converter = BTORConverter(environment, self.btor)
        self.mgr = environment.formula_manager
        self.declarations = {}
        return

# EOC BoolectorOptions

        pass

    @clear_pending_pop
    def _reset_assertions(self):
        self.btor = pyboolector.Boolector()
        self.options(self)
        self.converter = BTORConverter(self.environment, self.btor)
        self.declarations = {}

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
            btor_assumptions = [self.converter.convert(a) for a in assumptions]
            self.btor.Assume(*btor_assumptions)

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
        self.btor.Push(levels)

    @clear_pending_pop
    def _pop(self, levels=1):
        self.btor.Pop(levels)

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print("%s = %s" % (var.symbol_name(), self.get_value(var)))

    def get_value(self, item):
        self._assert_no_function_type(item)
        itype = item.get_type()
        titem = self.converter.convert(item)
        if itype.is_bv_type():
            return self.mgr.BV(titem.assignment, item.bv_width())
        elif itype.is_bool_type():
            return self.mgr.Bool(bool(int(titem.assignment)))
        else:
            assert itype.is_array_type()
            assert itype.index_type.is_bv_type()
            assert itype.elem_type.is_bv_type()

            idx_width = itype.index_type.width
            val_width = itype.elem_type.width
            assign = {}
            for (idx, val) in titem.assignment:
                assign[self.mgr.BV(idx, idx_width)] = self.mgr.BV(val, val_width)
            return self.mgr.Array(itype.index_type,
                                  self.mgr.BV(0, val_width), assign)

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
        assert len(args) >= 2
        res = self._btor.And(args[0], args[1])
        for conj in args[2:]:
            res = self._btor.And(res, conj)
        return res

    def walk_or(self, formula, args, **kwargs):
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
            res = self._btor.Var(self._btor.BitVecSort(1), formula.symbol_name())
        elif symbol_type.is_real_type():
            raise ConvertExpressionError
        elif symbol_type.is_int_type():
            raise ConvertExpressionError
        elif symbol_type.is_array_type():
            # BTOR supports only Arrays of Type (BV, BV)
            index_type = symbol_type.index_type
            elem_type = symbol_type.elem_type
            if not (index_type.is_bv_type() and elem_type.is_bv_type()):
                raise ConvertExpressionError("BTOR supports only Array(BV,BV). "\
                                             "Type '%s' was given." % str(symbol_type))
            res = self._btor.Array(self._btor.ArraySort(self._btor.BitVecSort(index_type.width),
                                                        self._btor.BitVecSort(elem_type.width)),
                                   formula.symbol_name())
        else:
            assert symbol_type.is_bv_type()
            res = self._btor.Var(self._btor.BitVecSort(formula.bv_width()),
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
        args = self._extend_bv_equal_width(*args)
        return self._btor.Eq(*args)

    def walk_function(self, formula, args, **kwargs):
        _uf = self.declare_function(formula)
        return _uf(*args)

    def walk_bv_constant(self, formula, **kwargs):
        value = to_python_integer(formula.constant_value())
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
        # LHS width must be a power of 2
        # Since this is a Logical Shift, we can Zero-Extend LHS
        # if this is not the case
        lhs, rhs = self._extend_bv_pow2(args[0]), args[1]
        lhs_w, rhs_w = lhs.width, rhs.width

        # Boolector requires that witdh(rhs) = log2(width(lhs))
        target_w = int(ceil(log(lhs_w, 2)))
        if rhs_w == target_w:
            return lhs << args[1]
        else:
            # If (rhs > max) Then 0 Else Rescale
            max_value = 2**target_w-1
            max_big = self._btor.Const(max_value, rhs_w)
            cond = self._btor.Ugt(rhs, max_big)
            zero = self._btor.Const(0, lhs_w)
            rescaled = self._btor.Slice(rhs, target_w-1, 0)
            return self._btor.Cond(cond,
                                   zero,
                                   self._btor.Sll(lhs, rescaled))

    def walk_bv_lshr(self, formula, args, **kwargs):
        # LHS width must be a power of 2
        # Since this is a Logical Shift, we can Zero-Extend LHS
        # if this is not the case
        lhs, rhs = self._extend_bv_pow2(args[0]), args[1]
        lhs_w, rhs_w = lhs.width, rhs.width
        target_w = int(ceil(log(lhs_w, 2)))

        # Boolector requires that width(rhs) = log2(width(lhs))
        if rhs_w == target_w:
            return lhs >> rhs
        else:
            # If (rhs > max) Then 0 Else Rescale
            max_value = 2**target_w-1
            max_big = self._btor.Const(max_value, rhs_w)
            cond = self._btor.Ugt(rhs, max_big)
            zero = self._btor.Const(0, lhs_w)
            rescaled = self._btor.Slice(rhs, target_w-1, 0)
            return self._btor.Cond(cond,
                                   zero,
                                   self._btor.Srl(lhs, rescaled))

    def walk_bv_rol(self, formula, args, **kwargs):
        return self._btor.Rol(args[0],
                             formula.bv_rotation_step())

    def walk_bv_ror(self, formula, args, **kwargs):
        return self._btor.Ror(args[0],
                             formula.bv_rotation_step())

    def walk_bv_zext(self, formula, args, **kwargs):
        return self._btor.Uext(args[0], formula.bv_extend_step())

    def walk_bv_sext(self, formula, args, **kwargs):
        return self._btor.Sext(args[0], formula.bv_extend_step())

    def walk_bv_slt(self, formula, args, **kwargs):
        return self._btor.Slt(args[0], args[1])

    def walk_bv_sle(self, formula, args, **kwargs):
        return self._btor.Slte(args[0], args[1])

    def walk_bv_comp(self, formula, args, **kwargs):
        return self._btor.Eq(args[0], args[1])

    def walk_bv_sdiv(self, formula, args, **kwargs):
        return self._btor.Sdiv(args[0], args[1])

    def walk_bv_srem(self, formula, args, **kwargs):
        return self._btor.Srem(args[0], args[1])

    def walk_bv_ashr (self, formula, args, **kwargs):
        # LHS width must be a power of 2
        # Since this is an Arithmetic Shift, we need to Sign-Extend LHS
        # if this is not the case
        lhs, rhs = self._extend_bv_pow2(args[0], signed=True), args[1]
        lhs_w, rhs_w = lhs.width, rhs.width

        # Boolector requires that witdh(rhs) = log2(width(lhs))
        target_w = int(ceil(log(lhs_w, 2)))
        if rhs_w == target_w:
            return self._btor.Sra(lhs, rhs)
        else:
            # IF (rhs <= max) Then Rescale Else Max
            max_value = 2**target_w-1
            max_big = self._btor.Const(max_value, rhs_w)
            cond = self._btor.Ulte(rhs, max_big)
            max_small = self._btor.Const(max_value, target_w)
            rescaled = self._btor.Slice(rhs, target_w-1, 0)
            return self._btor.Sra(lhs, self._btor.Cond(cond,
                                                       rescaled,
                                                       max_small))

    def walk_array_store(self, formula, args, **kwargs):
        return self._btor.Write(args[0], args[1], args[2])

    def walk_array_select(self, formula, args, **kwargs):
        return self._btor.Read(args[0], args[1])

    def walk_array_value(self, formula, args, **kwargs):
        raise ConvertExpressionError("btor does not support constant arrays")

    def _type_to_btor(self, tp):
        if tp.is_bool_type():
            return self._btor.BoolSort()
        elif tp.is_real_type():
            raise ConvertExpressionError
        elif tp.is_int_type():
            raise ConvertExpressionError
        elif tp.is_bv_type():
            return self._btor.BitVecSort(tp.width)
        elif tp.is_array_type():
            raise ConvertExpressionError("Unsupported Array Type")
        else:
            assert tp.is_function_type() , "Unsupported type '%s'" % tp
            stps = [self._type_to_btor(x) for x in tp.param_types]
            rtp = self._type_to_btor(tp.return_type)
            return self._btor.FunSort(stps, rtp)

    def _extend_bv_pow2(self, btor_formula, signed=False):
        """BTOR requires that many operands have width that is a power of 2"""
        w = btor_formula.width
        target_w = 2**int(ceil(log(w, 2)))
        # Skip if width is ok
        if target_w == w:
            return btor_formula
        if signed:
            return self._btor.Sext(btor_formula, (target_w-w))
        else:
            return self._btor.Uext(btor_formula, (target_w-w))

    def _extend_bv_equal_width(self, arg1, arg2):
        if arg1.width == arg2.width:
            return (arg1, arg2)
        elif arg1.width > arg2.width:
            ext = arg1.width - arg2.width
            return (arg1,
                    self._btor.Uext(arg2, ext))
        elif arg1.width < arg2.width:
            ext = arg2.width - arg1.width
            return (self._btor.Uext(arg1, ext),
                    arg2)
