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
from functools import partial

import pysmt.operators as op
import pysmt.exceptions


class Walker(object):

    def __init__(self, env=None):
        if env is None:
            import pysmt.environment
            env = pysmt.environment.get_env()
        self.env = env

        self.functions = {}
        self.functions[op.FORALL] = self.walk_forall
        self.functions[op.EXISTS] = self.walk_exists
        self.functions[op.AND] = self.walk_and
        self.functions[op.OR] = self.walk_or
        self.functions[op.NOT] = self.walk_not
        self.functions[op.IMPLIES] = self.walk_implies
        self.functions[op.IFF] = self.walk_iff
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_function
        self.functions[op.REAL_CONSTANT] = self.walk_real_constant
        self.functions[op.BOOL_CONSTANT] = self.walk_bool_constant
        self.functions[op.INT_CONSTANT] = self.walk_int_constant
        self.functions[op.PLUS] = self.walk_plus
        self.functions[op.MINUS] = self.walk_minus
        self.functions[op.TIMES] = self.walk_times
        self.functions[op.EQUALS] = self.walk_equals
        self.functions[op.LE] = self.walk_le
        self.functions[op.LT] = self.walk_lt
        self.functions[op.ITE] = self.walk_ite
        self.functions[op.TOREAL] = self.walk_toreal

        self.functions[op.BV_CONSTANT] = self.walk_bv_constant
        self.functions[op.BV_CONCAT] = self.walk_bv_concat
        self.functions[op.BV_EXTRACT] = self.walk_bv_extract
        self.functions[op.BV_NOT] = self.walk_bv_not
        self.functions[op.BV_AND] = self.walk_bv_and
        self.functions[op.BV_OR] = self.walk_bv_or
        self.functions[op.BV_XOR] = self.walk_bv_xor
        self.functions[op.BV_ULT] = self.walk_bv_ult
        self.functions[op.BV_ULE] = self.walk_bv_ule
        self.functions[op.BV_NEG] = self.walk_bv_neg
        self.functions[op.BV_ADD] = self.walk_bv_add
        self.functions[op.BV_SUB] = self.walk_bv_sub
        self.functions[op.BV_MUL] = self.walk_bv_mul
        self.functions[op.BV_UDIV] = self.walk_bv_udiv
        self.functions[op.BV_UREM] = self.walk_bv_urem
        self.functions[op.BV_LSHL] = self.walk_bv_lshl
        self.functions[op.BV_LSHR] = self.walk_bv_lshr
        self.functions[op.BV_ROL] = self.walk_bv_rol
        self.functions[op.BV_ROR] = self.walk_bv_ror
        self.functions[op.BV_ZEXT] = self.walk_bv_zext
        self.functions[op.BV_SEXT] = self.walk_bv_sext
        self.functions[op.BV_SLT] = self.walk_bv_slt
        self.functions[op.BV_SLE] = self.walk_bv_sle
        self.functions[op.BV_COMP] = self.walk_bv_comp
        self.functions[op.BV_SDIV] = self.walk_bv_sdiv
        self.functions[op.BV_SREM] = self.walk_bv_srem
        self.functions[op.BV_ASHR] = self.walk_bv_ashr

        self.functions[op.ARRAY_SELECT] = self.walk_array_select
        self.functions[op.ARRAY_STORE] = self.walk_array_store
        self.functions[op.ARRAY_VALUE] = self.walk_array_value

        undefined_types = set(op.ALL_TYPES) - set(self.functions.keys())
        assert len(undefined_types) == 0, \
            "The following types are not defined in the generic walker: {%s}" % \
            (", ".join(op.op_to_str(u) for u in undefined_types))


    def set_function(self, function, *node_types):
        """Overrides the default walking function for each of the specified
        node_types with the given function
        """
        for nt in node_types:
            self.functions[nt] = function


    def walk_error(self, formula, **kwargs):
        """ Default function for a node that is not handled by the Walker, by
        raising a NotImplementedError.
        """
        node_type = formula.node_type()
        if node_type in self.env.dwf:
            dwf = self.env.dwf[node_type]
            walker_class = type(self)
            if type(self) in dwf:
                self.functions[node_type] = partial(dwf[walker_class], self)
                return self.functions[node_type](formula, **kwargs)

        node_type = formula.node_type()
        raise pysmt.exceptions.UnsupportedOperatorError(node_type=node_type,
                                                        expression=formula)


    # Methods to be overwritten:
    # Formula will be provided in the key-word formula
    # Additional arguments are passed in the kwargs
    def walk_forall(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_exists(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_and(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_or(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_not(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_implies(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_iff(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_symbol(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_function(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_real_constant(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_bool_constant(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_int_constant(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_plus(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_minus(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_times(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_equals(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_le(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_lt(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_ite(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_toreal(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_constant(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_concat(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_extract(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_not(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_and(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_or(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_xor(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_ult(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_ule(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_comp(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_neg(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_add(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_sub(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_mul(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_udiv(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_urem(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_lshl(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_lshr(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_rol(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_ror(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_zext(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_sext(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_slt(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_sle(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_sdiv(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_srem(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_bv_ashr(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_array_select(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_array_store(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_array_value(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)
