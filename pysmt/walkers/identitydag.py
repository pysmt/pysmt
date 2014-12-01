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
from pysmt.walkers.dag import DagWalker

class IdentityDagWalker(DagWalker):
    """This class traverses a formula and rebuilds it recursively
    identically.

    This could be useful when only some nodes needs to be rewritten
    but the structure of the formula has to be kept.

    """


    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)

    def walk_symbol(self, formula, args):
        return self.env.formula_manager.Symbol(formula.symbol_name(),
                                               formula.symbol_type())

    def walk_real_constant(self, formula, args):
        return self.env.formula_manager.Real(formula.constant_value())

    def walk_int_constant(self, formula, args):
        return self.env.formula_manager.Int(formula.constant_value())

    def walk_bool_constant(self, formula, args):
        return self.env.formula_manager.Bool(formula.constant_value())

    def walk_and(self, formula, args):
        return self.env.formula_manager.And(args)

    def walk_or(self, formula, args):
        return self.env.formula_manager.Or(args)

    def walk_not(self, formula, args):
        return self.env.formula_manager.Not(args[0])

    def walk_iff(self, formula, args):
        return self.env.formula_manager.Iff(args[0], args[1])

    def walk_implies(self, formula, args):
        return self.env.formula_manager.Implies(args[0], args[1])

    def walk_equals(self, formula, args):
        return self.env.formula_manager.Equals(args[0], args[1])

    def walk_ite(self, formula, args):
        return self.env.formula_manager.Ite(args[0], args[1], args[2])

    def walk_ge(self, formula, args):
        return self.env.formula_manager.GE(args[0], args[1])

    def walk_le(self, formula, args):
        return self.env.formula_manager.LE(args[0], args[1])

    def walk_gt(self, formula, args):
        return self.env.formula_manager.GT(args[0], args[1])

    def walk_lt(self, formula, args):
        return self.env.formula_manager.LT(args[0], args[1])

    def walk_forall(self, formula, args):
        qvars = [self.walk_symbol(v, None) for v in formula.quantifier_vars()]
        return self.env.formula_manager.ForAll(qvars,args[0])

    def walk_exists(self, formula, args):
        qvars = [self.walk_symbol(v, None) for v in formula.quantifier_vars()]
        return self.env.formula_manager.Exists(qvars,args[0])

    def walk_plus(self, formula, args):
        return self.env.formula_manager.Plus(args)

    def walk_times(self, formula, args):
        return self.env.formula_manager.Times(args[0], args[1])

    def walk_minus(self, formula, args):
        return self.env.formula_manager.Minus(args[0], args[1])

    def walk_function(self, formula, args):
        return self.env.formula_manager.Function(formula.function_name(), args)

    def walk_toreal(self, formula, args):
        return self.env.formula_manager.ToReal(args[0])
