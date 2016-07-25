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
from pysmt.walkers import DagWalker
from pysmt.typing import EnumType


class EnumRewriter(DagWalker):
    """Rewrites a formula containing Enum types into an equisatisfiable one.

    The rewriting works by using:
    - Boolean variables (bit-blasting)
    - BitVectors
    - Integers

    The formula contains the domains preconditions in the form:
      domains -> f'
    """
    def walk_equals(self, formula, args, **kwargs):
        mgr = self.env.formula_manager
        left, right = args
        if left.is_symbol(type_=EnumType) and right.is_symbol(type_=EnumType):
            assert left.enum_type == right.enum_type
            # For each bit write:
            #    l[1] <-> r[1]
            #    l[2] <-> r[2]
            #    l[3] <-> r[3]
            total_bits = left.symbol_type().bit_count()
            res = []
            for i in xrange(total_bits):
                ls = left.ith_bit(i)
                rs = right.ith_bit(i)
                res.append(mgr.Iff(ls, rs))
            return mgr.And(res)
        elif left.is_symbol(type_=EnumSymbol) and right.is_constant(type_=EnumType):
            assert left.symbol_type() == right.constant_type()
            # Encode the value of EnumConst using the Symbol
            #   E.g., l[1] /\ !l[0] (Value #1)
            return self.encode_enum_constant(right, left)
        elif isinstance(left, EnumConst) and isinstance(right, EnumSymbol):
            assert left.enum_type == right.enum_type
            # See previous case
            return self.encode_enum_constant(left, right)
        elif isinstance(left, EnumConst) and isinstance(right, EnumConst):
            assert left.enum_type == right.enum_type
            return mgr.Bool(left.constant_value() == right.constant_value())
        else:
            raise TypeError

    def encode_enum_constant(self, const, symbol):
        enum_type = const.constant_type()
        total_bits = enum_type.bit_count()
        idx = enum_type.domain().index(const)
        res = []
        for i in xrange(total_bits):
            ls = symbol.ith_bit(i)
            if idx % 2 == 0:
                res.append(self.env.formula_manager.Not(ls))
            else:
                res.append(ls)
            idx = idx / 2
        return self.env.formula_manager.And(res)

    # def ith_bit(self, i):
    #     return Symbol("%s_$%d" % (self.name, i))

    # def encode_domain(self, symbol):
    #     values = [self.encode_value(symbol, value) for value in self.domain()]
    #     return Or(values)

    # def decode_value(self, symbol, model):
    #     idx = 0
    #     for i in xrange(self.bit_count()):
    #         if model.get_py_value(symbol.ith_bit(i)):
    #             idx = idx + (1 << i)



#EOC EnumRewriter
