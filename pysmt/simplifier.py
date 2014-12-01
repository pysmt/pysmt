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
import pysmt.walkers as walkers
import pysmt.operators as op
import pysmt.typing as types


class Simplifier(walkers.DagWalker):

    def __init__(self, env=None):
        walkers.DagWalker.__init__(self, env=env)
        self.manager = self.env.formula_manager

        self.functions[op.SYMBOL] = self.walk_identity
        self.functions[op.REAL_CONSTANT] = self.walk_identity
        self.functions[op.BOOL_CONSTANT] = self.walk_identity
        self.functions[op.INT_CONSTANT] = self.walk_identity

        self._validate_simplifications = None

    @property
    def validate_simplifications(self):
        return self._validate_simplifications

    @validate_simplifications.setter
    def validate_simplifications(self, value):
        if value:
            self.walk = self.walk_debug
        else:
            # Restore original walk method
            self.walk = type(Simplifier.walk)(Simplifier.walk, self, Simplifier)

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

        args = [self.walk(s, **kwargs) for s in formula.get_sons()]

        f = self.functions[formula.node_type()]
        res = f(formula, args, **kwargs)
        ltype = get_type(formula)
        rtype = get_type(res)
        test = Equals(formula, res) if ltype != BOOL else Iff(formula, res)
        assert (ltype == rtype) and is_valid(test, solver_name="z3"), \
               ("Was: %s \n Obtained: %s\n" % (str(formula), str(res)))
        return res


    def walk_and(self, formula, args):
        args = [x for x in args if not x.is_true()]
        if len(args) == 0:
            return self.manager.TRUE()
        elif len(args) == 1:
            return args[0]

        else:
            if any(x.is_false() for x in args):
                return self.manager.FALSE()

        return self.manager.And(args)


    def walk_or(self, formula, args):
        args = [x for x in args if not x.is_false()]
        if len(args) == 0:
            return self.manager.FALSE()
        elif len(args) == 1:
            return args[0]

        else:
            if any(x.is_true() for x in args):
                return self.manager.TRUE()

        return self.manager.Or(args)


    def walk_not(self, formula, args):
        assert len(args) == 1
        args = args[0]
        if args.is_bool_constant():
            l = args.constant_value()
            return self.manager.Bool(not l)
        elif args.is_not():
            return args.arg(0)

        return self.manager.Not(args)


    def walk_iff(self, formula, args):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_bool_constant() and sr.is_bool_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l == r)
        elif sl == sr:
            return self.manager.TRUE()
        else:
            return self.manager.Iff(sl, sr)

    def walk_implies(self, formula, args):
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


    def walk_equals(self, formula, args):
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

    def walk_ite(self, formula, args):
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

    def walk_ge(self, formula, args):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l >= r)

        return self.manager.GE(sl, sr)

    def walk_le(self, formula, args):
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

    def walk_gt(self, formula, args):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l > r)
        return self.manager.GT(sl, sr)

    def walk_lt(self, formula, args):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l < r)
        return self.manager.LT(sl, sr)


    def walk_forall(self, formula, args):
        assert len(args) == 1
        sf = args[0]

        varset = set(formula.quantifier_vars()).intersection(sf.get_dependencies())

        if len(varset) == 0:
            return sf

        return self.manager.ForAll(varset, sf)


    def walk_exists(self, formula, args):
        assert len(args) == 1
        sf = args[0]

        varset = set(formula.quantifier_vars()).intersection(sf.get_dependencies())

        if len(varset) == 0:
            return sf

        return self.manager.Exists(varset, sf)


    def walk_plus(self, formula, args):
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
            if ns[0].is_times():
                t = ns[0]
                if t.arg(0) == minus_one:
                    return self.manager.Minus(ns[1], t.arg(1))
                if t.arg(1) == minus_one:
                    return self.manager.Minus(ns[1], t.arg(0))
            # (+ Y (* -1 X)) => (- Y X)
            if ns[1].is_times():
                t = ns[1]
                if t.arg(0) == minus_one:
                    return self.manager.Minus(ns[0], t.arg(1))
                if t.arg(1) == minus_one:
                    return self.manager.Minus(ns[0], t.arg(0))

        if len(ns) == 1:
            return ns[0]
        return self.manager.Plus(ns)


    def walk_times(self, formula, args):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            if sl.is_real_constant():
                return self.manager.Real(l * r)
            else:
                assert sl.is_int_constant()
                return self.manager.Int(l * r)

        if sl.is_constant():
            if sl.is_one():
                return sr
            elif sl.is_zero():
                if sl.is_real_constant():
                    return self.manager.Real(0)
                else:
                    assert sl.is_int_constant()
                    return self.manager.Int(0)

        if sr.is_constant():
            if sr.is_one():
                return sl
            elif sr.is_zero():
                if sr.is_real_constant():
                    return self.manager.Real(0)
                else:
                    assert sr.is_int_constant()
                    return self.manager.Int(0)

        return self.manager.Times(sl, sr)



    def walk_minus(self, formula, args):
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


    def walk_function(self, formula, args):
        return self.manager.Function(formula.function_name(), args)

    def walk_toreal(self, formula, args):
        assert len(args) == 1
        if args[0].is_constant():
            assert args[0].is_int_constant()
            return self.manager.Real(args[0].constant_value())
        return self.manager.ToReal(args[0])


 # EOC Simplifier
