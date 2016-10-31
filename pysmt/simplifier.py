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

import pysmt.walkers
import pysmt.operators as op
import pysmt.typing as types
from pysmt.utils import set_bit
from pysmt.exceptions import PysmtValueError
from pysmt.constants import Numeral, pysmt_integer_from_integer


class Simplifier(pysmt.walkers.DagWalker):
    """Perform basic simplifications of the input formula."""

    def __init__(self, env=None):
        pysmt.walkers.DagWalker.__init__(self, env=env)
        self.manager = self.env.formula_manager

        self.set_function(self.walk_identity, op.SYMBOL, op.REAL_CONSTANT,
                          op.INT_CONSTANT, op.BOOL_CONSTANT, op.BV_CONSTANT,
                          op.ALGEBRAIC_CONSTANT)

        self._validate_simplifications = None
        self.original_walk = self.walk

    @property
    def validate_simplifications(self):
        return self._validate_simplifications

    @validate_simplifications.setter
    def validate_simplifications(self, value):
        """If set to true: checks for equivalence after each simplification.

        NOTE: This can be very expensive, and should be used for debug
        and testing only.
        """
        if value:
            self.walk = self.walk_debug
        else:
            # Restore original walk method
            self.walk = self.original_walk

        self._validate_simplifications = value

    def simplify(self, formula):
        """Performs simplification of the given formula."""
        return self.walk(formula)

    def _get_key(self, formula, **kwargs):
        return formula

    def walk_debug(self, formula, **kwargs):
        from pysmt.shortcuts import Equals, Iff, get_type, is_valid
        from pysmt.typing import BOOL

        if formula in self.memoization:
            return self.memoization[formula]

        args = [self.walk(s, **kwargs) for s in formula.args()]

        f = self.functions[formula.node_type()]
        res = f(formula, args=args, **kwargs)
        ltype = get_type(formula)
        rtype = get_type(res)
        test = Equals(formula, res) if ltype != BOOL else Iff(formula, res)
        assert (ltype == rtype) and is_valid(test, solver_name="z3"), \
               ("Was: %s \n Obtained: %s\n" % (str(formula), str(res)))
        return res

    def walk_and(self, formula, args, **kwargs):
        args = [x for x in args if not x.is_true()]
        if len(args) == 0:
            return self.manager.TRUE()
        elif len(args) == 1:
            return args[0]
        else:
            if any(x.is_false() for x in args):
                return self.manager.FALSE()

        return self.manager.And(args)

    def walk_or(self, formula, args, **kwargs):
        args = [x for x in args if not x.is_false()]
        if len(args) == 0:
            return self.manager.FALSE()
        elif len(args) == 1:
            return args[0]
        else:
            if any(x.is_true() for x in args):
                return self.manager.TRUE()

        return self.manager.Or(args)

    def walk_not(self, formula, args, **kwargs):
        assert len(args) == 1
        args = args[0]
        if args.is_bool_constant():
            l = args.constant_value()
            return self.manager.Bool(not l)
        elif args.is_not():
            return args.arg(0)

        return self.manager.Not(args)

    def walk_iff(self, formula, args, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_bool_constant() and sr.is_bool_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l == r)
        elif sl.is_bool_constant():
            if sl.constant_value():
                return sr
            else:
                return self.manager.Not(sr)
        elif sr.is_bool_constant():
            if sr.constant_value():
                return sl
            else:
                return self.manager.Not(sl)
        elif sl == sr:
            return self.manager.TRUE()
        else:
            return self.manager.Iff(sl, sr)

    def walk_implies(self, formula, args, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_bool_constant():
            l = sl.constant_value()
            if l:
                return sr
            else:
                return self.manager.TRUE()
        elif sr.is_bool_constant():
            r = sr.constant_value()
            if r:
                return self.manager.TRUE()
            else:
                return self.manager.Not(sl)
        elif sl == sr:
            return self.manager.TRUE()
        else:
            return self.manager.Implies(sl, sr)

    def walk_equals(self, formula, args, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l == r)
        elif sl == sr:
            return self.manager.TRUE()
        else:
            return self.manager.Equals(sl, sr)

    def walk_ite(self, formula, args, **kwargs):
        assert len(args) == 3
        si = args[0]
        st = args[1]
        se = args[2]

        if st == se:
            return st
        elif si.is_bool_constant():
            if si.constant_value():
                return st
            else:
                return se
        else:
            return self.manager.Ite(si, st, se)

    def walk_le(self, formula, args, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l <= r)

        # # (le 0 (- X Y)) => (le Y X)
        if sl.is_zero() and sr.is_minus():
            x, y = sr.arg(0), sr.arg(1)
            return self.manager.LE(y, x)
        # (le (- X Y) 0) => (le X Y)
        if sr.is_zero() and sr.is_minus():
            x, y = sr.arg(0), sr.arg(1)
            return self.manager.LE(x, y)
        return  self.manager.LE(sl, sr)

    def walk_lt(self, formula, args, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l < r)
        return self.manager.LT(sl, sr)

    def walk_forall(self, formula, args, **kwargs):
        assert len(args) == 1
        sf = args[0]

        varset = set(formula.quantifier_vars()).intersection(sf.get_free_variables())

        if len(varset) == 0:
            return sf

        return self.manager.ForAll(varset, sf)

    def walk_exists(self, formula, args, **kwargs):
        assert len(args) == 1
        sf = args[0]

        varset = set(formula.quantifier_vars()).intersection(sf.get_free_variables())

        if len(varset) == 0:
            return sf

        return self.manager.Exists(varset, sf)

    def walk_plus(self, formula, args, **kwargs):
        is_real = any(x.is_real_constant() for x in args)
        is_int = any(x.is_int_constant() for x in args)
        assert not (is_real and is_int)

        if all(x.is_constant() for x in args):
            res = sum(x.constant_value() for x in args)
            if is_real:
                return self.manager.Real(res)
            else:
                return self.manager.Int(res)

        ns = [x for x in args if not x.is_constant()]
        if len(ns) < len(args):
            num = sum(x.constant_value() for x in args if x.is_constant())
            if num != 0:
                if is_real:
                    ns.append(self.manager.Real(num))
                else:
                    ns.append(self.manager.Int(num))

        if len(ns) == 2:
            minus_one = self.manager.Real(-1) if is_real else \
                        self.manager.Int(-1)
            # (+ (* -1 X) Y) => (- Y X)
            if ns[0].is_times() and len(ns[0].args()) == 2:
                t = ns[0]
                if t.arg(0) == minus_one:
                    return self.manager.Minus(ns[1], t.arg(1))
                if t.arg(1) == minus_one:
                    return self.manager.Minus(ns[1], t.arg(0))
            # (+ Y (* -1 X)) => (- Y X)
            if ns[1].is_times() and len(ns[0].args()) == 2:
                t = ns[1]
                if t.arg(0) == minus_one:
                    return self.manager.Minus(ns[0], t.arg(1))
                if t.arg(1) == minus_one:
                    return self.manager.Minus(ns[0], t.arg(0))

        if len(ns) == 1:
            return ns[0]
        return self.manager.Plus(ns)

    def walk_times(self, formula, args, **kwargs):
        new_args = []
        constant_mul = 1
        stack = list(args)
        ttype = self.env.stc.get_type(args[0])
        is_algebraic = False
        while len(stack) > 0:
            x = stack.pop()
            if x.is_constant():
                if x.is_algebraic_constant():
                    is_algebraic = True
                if x.is_zero():
                    constant_mul = 0
                    break
                else:
                    constant_mul *= x.constant_value()
            elif x.is_times():
                stack += x.args()
            else:
                new_args.append(x)

        const = None
        if is_algebraic:
            const = self.manager._Algebraic(Numeral(constant_mul))
        elif ttype.is_real_type():
            const = self.manager.Real(constant_mul)
        else:
            assert ttype.is_int_type()
            const = self.manager.Int(constant_mul)

        if const.is_zero():
            return const
        else:
            if len(new_args) == 0:
                return const
            elif not const.is_one():
                new_args.append(const)

        return self.manager.Times(new_args)


    def walk_pow(self, formula, args, **kwargs):
        if args[0].is_constant():
            base = args[0].constant_value()
            exp = args[1].constant_value()
            int_exp = pysmt_integer_from_integer(exp)
            if exp.constant_value() == int_exp:
                # If the exponent cannot be represented as an integer,
                # we do not perform simplification.
                # A more accurate analysis would be to check wheter
                # base ** exp is a rational number.
                exp = int_exp
                if args[0].is_real_constant():
                    return self.manager.Real(base**exp)
                elif args[0].is_int_constant():
                    return self.manager.Int(base**exp)
        return self.manager.Pow(args[0], args[1])

    def walk_minus(self, formula, args, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_real_constant() and sr.is_real_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Real(l - r)

        if sl.is_int_constant() and sr.is_int_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Int(l - r)

        if sr.is_constant() and sr.is_zero():
            return sl

        if sl == sr:
            if self.env.stc.walk(sl) == types.REAL:
                return self.manager.Real(0)
            else:
                return self.manager.Int(0)

        return self.manager.Minus(sl, sr)

    def walk_function(self, formula, args, **kwargs):
        return self.manager.Function(formula.function_name(), args)

    def walk_toreal(self, formula, args, **kwargs):
        assert len(args) == 1
        if args[0].is_constant():
            assert args[0].is_int_constant()
            return self.manager.Real(args[0].constant_value())
        return self.manager.ToReal(args[0])

    def walk_bv_and(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            lhs = args[0].constant_value()
            rhs = args[1].constant_value()
            res = lhs & rhs
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVAnd(args[0], args[1])

    def walk_bv_not(self, formula, args, **kwargs):
        if args[0].is_bv_constant():
            res = ~args[0].constant_value() & (2**formula.bv_width() - 1)
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVNot(args[0])

    def walk_bv_neg(self, formula, args, **kwargs):
        if args[0].is_bv_constant():
            res = 2**formula.bv_width() - args[0].constant_value()
            res = res % 2**formula.bv_width()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVNeg(args[0])

    def walk_bv_or(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].constant_value() | args[1].constant_value()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVOr(args[0], args[1])

    def walk_bv_xor(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].constant_value() ^ args[1].constant_value()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVXor(args[0], args[1])

    def walk_bv_add(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].constant_value() + args[1].constant_value()
            res = res % 2**formula.bv_width()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVAdd(args[0], args[1])

    def walk_bv_mul(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].constant_value() * args[1].constant_value()
            res = res % 2**formula.bv_width()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVMul(args[0], args[1])

    def walk_bv_udiv(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            if args[1].bv_unsigned_value() == 0:
                res = 2**formula.bv_width() - 1
            else:
                res = args[0].bv_unsigned_value() // args[1].bv_unsigned_value()
                res = res % 2**formula.bv_width()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVUDiv(args[0], args[1])

    def walk_bv_urem(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            if args[1].bv_unsigned_value() == 0:
                res = args[0].bv_unsigned_value()
            else:
                res = args[0].bv_unsigned_value() % args[1].bv_unsigned_value()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVURem(args[0], args[1])

    def walk_bv_ult(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].bv_unsigned_value() < args[1].bv_unsigned_value()
            return self.manager.Bool(res)
        return self.manager.BVULT(args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].bv_unsigned_value() <= args[1].bv_unsigned_value()
            return self.manager.Bool(res)
        return self.manager.BVULE(args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        if args[0].is_bv_constant():
            bitstr = args[0].bv_bin_str(reverse=True)
            start = formula.bv_extract_start()
            end = formula.bv_extract_end()
            res = bitstr[start:end+1][::-1]
            w = (end+1)-start
            return self.manager.BV("#b%s" % res, width=w)
        return self.manager.BVExtract(args[0],
                                      start=formula.bv_extract_start(),
                                      end=formula.bv_extract_end())

    def walk_bv_ror(self, formula, args, **kwargs):
        if args[0].is_bv_constant():
            bitstr = args[0].bv_bin_str(reverse=True)
            # Takes first k elements and move to end
            slice1 = bitstr[0:formula.bv_rotation_step()]
            slice2 = bitstr[formula.bv_rotation_step():]
            res = (slice2 + slice1)[::-1]
            return self.manager.BV(res)
        return self.manager.BVRor(args[0], formula.bv_rotation_step())

    def walk_bv_rol(self, formula, args, **kwargs):
        if args[0].is_bv_constant():
            bitstr = args[0].bv_bin_str(reverse=True)
            # Takes last k elements and move to beginning
            slice1 = bitstr[0:-formula.bv_rotation_step()]
            slice2 = bitstr[-formula.bv_rotation_step():]
            res = (slice2 + slice1)[::-1]
            return self.manager.BV(res)
        return self.manager.BVRol(args[0], formula.bv_rotation_step())

    def walk_bv_sext(self, formula, args, **kwargs):
        if args[0].is_bv_constant():
            bitstr = args[0].bv_bin_str()
            filler = bitstr[0]
            res = filler*formula.bv_extend_step() + bitstr
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVSExt(args[0], formula.bv_extend_step())

    def walk_bv_zext(self, formula, args, **kwargs):
        if args[0].is_bv_constant():
            bitstr = args[0].bv_bin_str()
            filler = "0"
            res = filler*formula.bv_extend_step() + bitstr
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVZExt(args[0], formula.bv_extend_step())

    def walk_bv_concat(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            w0 = args[0].bv_width()
            w1 = args[1].bv_width()
            res = (2**w1) * args[0].bv_unsigned_value() + \
                  args[1].bv_unsigned_value()
            return self.manager.BV(res, w1 + w0)
        return self.manager.BVConcat(args[0], args[1])

    def walk_bv_lshl(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].bv_unsigned_value() << args[1].bv_unsigned_value()
            w = args[0].bv_width()
            return self.manager.BV(res % (2 ** w), w)
        return self.manager.BVLShl(args[0], args[1])

    def walk_bv_lshr(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].bv_unsigned_value() >> args[1].bv_unsigned_value()
            w = args[0].bv_width()
            return self.manager.BV(res % (2 ** w), w)
        return self.manager.BVLShr(args[0], args[1])

    def walk_bv_sub(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].constant_value() - args[1].constant_value()
            res = res % 2**formula.bv_width()
            return self.manager.BV(res, width=formula.bv_width())
        return self.manager.BVSub(args[0], args[1])

    def walk_bv_slt(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].bv_signed_value() < args[1].bv_signed_value()
            return self.manager.Bool(res)
        return self.manager.BVSLT(args[0], args[1])

    def walk_bv_sle(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            res = args[0].bv_signed_value() <= args[1].bv_signed_value()
            return self.manager.Bool(res)
        return self.manager.BVSLE(args[0], args[1])

    def walk_bv_comp(self, formula, args, **kwargs):
        sl, sr = args

        if sl == sr:
            return self.manager.BV(1, 1)
        elif sl.is_bv_constant() and sr.is_bv_constant():
            return self.manager.BV(0, 1)
        else:
            return self.manager.BVComp(sl, sr)

    def walk_bv_sdiv(self, formula, args, **kwargs):
        l,r = args
        if l.is_bv_constant() and r.is_bv_constant():
            l_sign = l.bv_signed_value() < 0
            r_sign = r.bv_signed_value() < 0
            if (not l_sign) and (not r_sign):
                return self.walk_bv_udiv(self.manager.BVUDiv(l,r), args, **kwargs)
            elif l_sign and (not r_sign):
                nl = self.walk_bv_neg(self.manager.BVNeg(l), [l], **kwargs)
                div = self.walk_bv_udiv(self.manager.BVUDiv(nl, r), [nl, r],
                                        **kwargs)
                return self.walk_bv_neg(self.manager.BVNeg(div), [div], **kwargs)
            elif (not l_sign) and r_sign:
                nr = self.walk_bv_neg(self.manager.BVNeg(r), [r], **kwargs)
                div = self.walk_bv_udiv(self.manager.BVUDiv(l, nr), [l, nr],
                                        **kwargs)
                return self.walk_bv_neg(self.manager.BVNeg(div), [div], **kwargs)
            else:
                nl = self.walk_bv_neg(self.manager.BVNeg(l), [l], **kwargs)
                nr = self.walk_bv_neg(self.manager.BVNeg(r), [r], **kwargs)
                return self.walk_bv_udiv(self.manager.BVUDiv(nl, nr), [nl, nr],
                                         **kwargs)
        return self.manager.BVSDiv(l, r)

    def walk_bv_srem(self, formula, args, **kwargs):
        if args[0].is_bv_constant() and args[1].is_bv_constant():
            l = args[0]
            if args[0].bv_signed_value() < 0:
                l = self.walk_bv_neg(self.manager.BVNeg(args[0]), [args[0]],
                                     **kwargs)

            r = args[1]
            if args[1].bv_signed_value() < 0:
                r = self.walk_bv_neg(self.manager.BVNeg(args[1]), [args[1]],
                                     **kwargs)


            res = self.walk_bv_urem(self.manager.BVURem(l, r), [l, r],
                                    **kwargs)

            if args[0].bv_signed_value() < 0:
                res = self.walk_bv_neg(self.manager.BVNeg(res), [res],
                                       **kwargs)
            return res
        return self.manager.BVSRem(args[0], args[1])

    def walk_bv_ashr(self, formula, args, **kwargs):
        l,r = args
        if l.is_bv_constant() and r.is_bv_constant():
            sign = l.bv_signed_value() < 0
            ret = self.walk_bv_lshr(self.manager.BVLShr(l, r), [l, r], **kwargs)
            width = formula.bv_width()
            if sign:
                n = ret.bv_unsigned_value()
                padlen = width
                if width > r.bv_unsigned_value():
                    padlen = r.bv_unsigned_value()

                for i in xrange(width-padlen, width):
                    n = set_bit(n, i, True)
                ret = self.manager.BV(n, width)
            return ret
        return self.manager.BVAShr(l, r)

    def walk_array_select(self, formula, args, **kwargs):
        a, i = args
        if a.is_array_value() and i.is_constant():
            return a.array_value_get(i)
        return self.manager.Select(args[0], args[1])

    def walk_array_store(self, formula, args, **kwargs):
        a, i, v = args
        if a.is_array_value() and i.is_constant():
            assign = a.array_value_assigned_values_map()
            assign[i] = v # Add / Overwrite assignment at index i
            return self.manager.Array(a.array_value_index_type(),
                                      a.array_value_default(),
                                      assign)
        return self.manager.Store(a, i, v)

    def walk_array_value(self, formula, args, **kwargs):
        assign = dict(zip(args[1::2], args[2::2]))
        return self.manager.Array(formula.array_value_index_type(),
                                  args[0],
                                  assign)

    def walk_div(self, formula, args, **kwargs):
        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            if sl.is_real_constant():
                return self.manager.Real(l / r)
            else:
                assert sl.is_int_constant()
                return self.manager.Int(l / r)

        if sl.is_constant():
            if sl.is_zero():
                return sl

        if sr.is_constant():
            if sr.is_one():
                return sl

        return self.manager.Div(sl, sr)

# EOC Simplifier


class BddSimplifier(Simplifier):
    """A simplifier relying on BDDs.

    The formula is translated into a BDD and then translated back into
    a pySMT formula. This is a much more expensive simplification
    process, and might not work with formulas with thousands of
    boolean variables.

    The option ``static_ordering`` can be used to provide a variable
    ordering for the underlying bdd.

    The option ``bool_abstraction`` controls how to behave if the
    input formula contains Theory terms (i.e., is not purely boolean).
    If this option is False (default) an exception will be thrown when
    a Theory atom is found. If it is set to True, the Theory part is
    abstracted, and the simplification is performed only on the
    boolean structure of the formula.
    """

    def __init__(self, env=None, static_ordering=None, bool_abstraction=False):
        Simplifier.__init__(self, env=env)
        self.super_functions = dict(self.functions)
        self._validation_sname = None

        Solver = self.env.factory.Solver
        if static_ordering is not None:
            solver_options={'static_ordering': static_ordering}
        else:
            solver_options={'dynamic_reordering': True}
        self.s = Solver(name="bdd", solver_options=solver_options)
        self.convert = self.s.converter.convert
        self.back = self.s.converter.back
        # Set methods for boolean_abstraction
        self.bool_abstraction = bool_abstraction
        self.set_function(self.walk_simplify_and_abstract, *op.RELATIONS)
        self.set_function(self.walk_abstract_function, op.FUNCTION)
        self.ba_map = {}
        self.get_type = self.env.stc.get_type
        self.FreshSymbol = self.env.formula_manager.FreshSymbol

    @property
    def validate_simplifications(self):
        return self._validate_simplifications

    @validate_simplifications.setter
    def validate_simplifications(self, value):
        possible_solvers = [sname for sname in self.env.factory.all_solvers()\
                            if sname!="bdd"]
        if len(possible_solvers) == 0:
            raise PysmtValueError("To validate at least another solver must "
                                  "be available!")
        self._validation_sname = possible_solvers[0]
        self._validate_simplifications = value

    def simplify(self, formula):
        from pysmt.oracles import get_logic
        from pysmt.logics import BOOL, QF_BOOL
        if self.bool_abstraction:
            logic = get_logic(formula)
            if logic > QF_BOOL and logic != BOOL:
                res = self.abstract_and_simplify(formula)
            else:
                res = self.back(self.convert(formula))
        else:
            res = self.back(self.convert(formula))
        self._validate(formula, res)
        return res

    def _validate(self, old, new):
        if self.validate_simplifications:
            Iff = self.env.formula_manager.Iff
            is_valid = self.env.factory.is_valid
            sname = self._validation_sname
            assert is_valid(Iff(old, new), solver_name=sname ), \
              "Was: %s \n Obtained: %s\n" % (str(old), str(new))

    def abstract_and_simplify(self, formula):
        abs_formula = self.walk(formula)
        abs_res = self.back(self.convert(abs_formula))
        print(formula, abs_formula, abs_res)
        res = abs_res.substitute(self.ba_map)
        return res

    def walk_simplify_and_abstract(self, formula, args, **kwargs):
        super_rewriter = self.super_functions[formula.node_type()]
        rewritten = super_rewriter(formula, args, **kwargs)
        print(rewritten)
        if rewritten.is_bool_constant():
            return rewritten
        new_var = self.FreshSymbol()
        self.ba_map[new_var] = rewritten
        return new_var

    def walk_abstract_function(self, formula, args, **kwargs):
        super_rewriter = self.super_functions[formula.node_type()]
        rewritten = super_rewriter(formula, args, **kwargs)
        if rewritten.function_name().symbol_type().return_type.is_bool_type():
            new_var = self.FreshSymbol()
            self.ba_map[new_var] = rewritten
            return new_var
        return rewritten

#EOC BddSimplifier
