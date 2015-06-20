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
import random

import pysmt.operators as operators
from pysmt.shortcuts import And, Or, Symbol, Not, Implies, Iff, \
                            Minus, Plus, Times, Equals, \
                            LE, LT, Ite, Real, TRUE, FALSE, Int, \
                            ForAll, Exists
from pysmt.typing import BOOL, REAL, INT
from pysmt.decorators import deprecated


class Randomizer(object):

    @deprecated("No alternative.")
    def __init__(self, symbols_count, max_arity,
                 symbols_intro_ratio, seed=None,
                 available_ops=None):
        self.seed = seed
        self.symbols_count = symbols_count
        self.max_arity = max_arity
        self.symbols_intro_ratio = symbols_intro_ratio

        random.seed(seed)

        self.functions = {}
        self.functions[operators.AND] = self.rand_and
        self.functions[operators.BOOL_CONSTANT] = self.rand_bool_constant
        self.functions[operators.REAL_CONSTANT] = self.rand_real_constant
        self.functions[operators.INT_CONSTANT] = self.rand_int_constant
        self.functions[operators.EXISTS] = self.rand_exists
        self.functions[operators.EQUALS] = self.rand_equals
        self.functions[operators.FORALL] = self.rand_forall
        self.functions[operators.FUNCTION] = self.rand_error
        self.functions[operators.ITE] = self.rand_ite
        self.functions[operators.LE] = self.rand_le
        self.functions[operators.LT] = self.rand_lt
        self.functions[operators.MINUS] = self.rand_minus
        self.functions[operators.NOT] = self.rand_not
        self.functions[operators.OR] = self.rand_or
        self.functions[operators.PLUS] = self.rand_plus
        self.functions[operators.SYMBOL] = self.rand_symbol
        self.functions[operators.TIMES] = self.rand_times
        self.functions[operators.IMPLIES] = self.rand_implies
        self.functions[operators.IFF] = self.rand_iff

        # Define which operators have a particular type:
        self.operators_per_type = {}
        self.operators_per_type[BOOL] = [
                                         operators.AND,
                                         operators.BOOL_CONSTANT,
                                         operators.EXISTS,
                                         operators.FORALL,
                                         operators.ITE,
                                         operators.NOT,
                                         operators.OR,
                                         operators.SYMBOL,
                                         operators.LE,
                                         operators.LT,
                                         operators.IMPLIES,
                                         operators.IFF,
                                         operators.EQUALS,
                                        ]
        self.operators_per_type[REAL] = [
                                         operators.REAL_CONSTANT,
                                         operators.MINUS,
                                         operators.PLUS,
                                         operators.TIMES,
                                         operators.SYMBOL,
                                         operators.ITE,
#                                         operators.FORALL,
#                                         operators.EXISTS,
                                        ]

        self.operators_per_type[INT] = [
                                         operators.INT_CONSTANT,
                                         operators.MINUS,
                                         operators.PLUS,
                                         operators.TIMES,
                                         operators.SYMBOL,
                                         operators.ITE,
#                                         operators.FORALL,
#                                         operators.EXISTS,
                                        ]


        self.available_operators = available_ops
        # Refine available operators
        if available_ops:
            for type_ in self.operators_per_type:
                self.operators_per_type[type_] = \
                 [ op for op in self.operators_per_type[type_]
                        if op in available_ops ]

    def rand_binary(self, nc, constructor, type_):
        left = self.rand_formula(nc-1, type_)
        right = self.rand_formula(nc-1, type_)
        return constructor(left, right)

    def rand_nary(self, nc, constructor, type_):
        children_count = random.randrange(1, self.max_arity)
        if constructor == Plus and children_count == 1:
            children_count = 2
        args = [self.rand_formula(nc-1, type_)
                for _ in range(children_count)]
        return constructor(args)

    def real_nary(self, nc, constructor):
        return self.rand_nary(nc, constructor, REAL)

    def bool_nary(self, nc, constructor):
        return self.rand_nary(nc, constructor, BOOL)

    def int_nary(self, nc, constructor):
        return self.rand_nary(nc, constructor, INT)

    def rand_formula(self, nc, type_=BOOL):
        # randomly chose whether we have a sub-formula or a symbol
        is_symbol = False
        if nc == 0:
            is_symbol = True
        else:
            is_symbol = random.random() <= self.symbols_intro_ratio

        if is_symbol:
            sf = self.rand_symbol(type_)
        else:
            sf = self._random_subformula(nc, type_)

        return sf

    def _random_subformula(self, nc, type_):
        op = None
        # Pick random operator of the correct type
        ops = self.operators_per_type[type_]
        if len(ops)>0:
            op = random.choice(ops)
        else:
            assert False, "Type was %s, ops were %s" %(type_,ops)

        if op == operators.SYMBOL: # TODO: Generalize this
            sf = self.functions[op](type_)
        else:
            sf = self.functions[op](nc, type_)
        assert sf is not None, "Op: %s, NC: %d" % (op, nc)
        return sf

    # Specific random generators start here
    def rand_error(self, nc):
        raise NotImplementedError

    def rand_type(self):
        return random.choice([REAL, BOOL, INT])

    def rand_symbol(self, type_):
        return Symbol(str(random.randrange(0, self.symbols_count))+("_%s"%str(type_)), type_)

    def rand_and(self, nc, type_):
        assert type_ == BOOL
        return self.bool_nary(nc, And)

    def rand_bool_constant(self, _, type_):
        assert type_ == BOOL
        return random.choice([TRUE(), FALSE()])

    def rand_real_constant(self, _, type_):
        assert type_ == REAL
        n = random.randrange(1,10)
        d = random.randrange(1,10)
        return Real((n,d))

    def rand_int_constant(self, _, type_):
        assert type_ == INT
        n = random.randrange(1,10)
        return Int(int(n))

    def rand_exists(self, nc, type_):
        assert type_ == BOOL
        return self.rand_quantifier(nc, Exists)

    def rand_forall(self, nc, type_):
        assert type_ == BOOL
        return self.rand_quantifier(nc, ForAll)

    def rand_quantifier(self, nc, constructor):
        # Random variable set
        varlst = [ self.rand_symbol(BOOL) for _ in range(5) ]
        return constructor(varlst, self.rand_formula(nc-1, BOOL))

    def rand_equals(self, nc, _):
        new_type = random.choice([REAL, INT])
        return self.rand_binary(nc, Equals, new_type)

    def rand_implies(self, nc, type_):
        assert type_ == BOOL
        return self.rand_binary(nc, Implies, type_)

    def rand_iff(self, nc, _):
        return self.rand_binary(nc, Iff, BOOL)

    def rand_ite(self, nc, type_):
        i = self.rand_formula(nc-1, BOOL)
        t = self.rand_formula(nc-1, type_)
        e = self.rand_formula(nc-1, type_)
        return Ite(i,t,e)

    def rand_le(self, nc, _):
        new_type = random.choice([REAL, INT])
        return self.rand_binary(nc, LE, new_type)

    def rand_lt(self, nc, _):
        new_type = random.choice([REAL, INT])
        return self.rand_binary(nc, LT, new_type)

    def rand_minus(self, nc, type_):
        return self.rand_binary(nc, Minus, type_)

    def rand_not(self, nc, _):
        return Not(self.rand_formula(nc-1, BOOL))

    def rand_or(self, nc, type_):
        return self.rand_nary(nc, Or, type_)

    def rand_plus(self, nc, type_):
        return self.rand_nary(nc, Plus, type_)

    def rand_times(self, nc, type_):
        return self.rand_linear_binary(nc, Times, type_)

    def rand_linear_binary(self, nc, constructor, type_):
        if type_ == REAL:
            const = self.rand_real_constant(nc, type_)
        else:
            const = self.rand_int_constant(nc, type_)
        expr = self.rand_formula(nc-1, type_)
        return constructor(expr, const)


# EOC
@deprecated("No alternative.")
def build_random_formula(symbols_count, nestings_count,
                         max_arity, symbols_intro_ratio,
                         type_=BOOL, seed=None, available_ops=None):
    """ Simple wrapper around Randomizer to generate a random formula.

    The formula is randomly generated using the following parameters:
     - symbols_count: How many new symbol names can be defined;
     - nestings_count: How deep the tree of the formula can be;
     - max_arity: For n-ary operators, defines the max arity
     - symbols_intro_ratio: How often a subformula consists only of a symbol,
                            this is a value from 0 to 1. If set to 0, only leaf
                            nodes will be symbols.
     - type_: type of the resulting formula (Default: BOOL)
     - seed: Fix the seed for reproducibility (Default: None)
     - available_ops: A list containing the operators that can be used.
                      By default all operators defined in the randomizer are
                      used (Default: None)
    """
    r = Randomizer(symbols_count, max_arity,
                   symbols_intro_ratio, seed=seed, available_ops=available_ops)
    return r.rand_formula(nestings_count, type_)

@deprecated("No alternative.")
def build_random_qf_formula(symbols_count, nestings_count,
                            max_arity, symbols_intro_ratio,
                            type_=BOOL, seed=None, available_ops=None):
    """ Returns a quantifier free random formula. """

    qf_operators = [ op for op in operators.ALL_TYPES
                        if op not in [operators.FORALL, operators.EXISTS]]

    return build_random_formula(symbols_count=symbols_count,
                                nestings_count=nestings_count,
                                max_arity=max_arity,
                                symbols_intro_ratio=symbols_intro_ratio,
                                type_=type_,
                                seed=seed,
                                available_ops=qf_operators)
