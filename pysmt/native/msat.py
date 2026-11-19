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
"""FNodes backed by MathSAT terms.

MSatFormulaManager builds every node directly as a MathSAT term, and
MSatFNode answers the FNode API by decoding that term. The structure is
the one MathSAT returns (e.g., LT(a, b) is NOT(LE(b, a))), so formulae
are logically equivalent to, but not shaped like, the plain pysmt ones.
"""
from typing import Any, Dict, Optional, Tuple

import pysmt.operators as op
import pysmt.typing as types
from pysmt.constants import Fraction, pysmt_integer_from_integer
from pysmt.exceptions import (PysmtTypeError, ConvertExpressionError,
                              InternalSolverError)
from pysmt.fnode import FNode, FNodeContent
from pysmt.formula import FormulaManager
from pysmt.solvers.dynmsat import MSATLibLoader
from pysmt.solvers.msat import MSatConverter, MSatEnv

_lib = MSATLibLoader("mathsat")

# Constructs that have no MathSAT term (Q7 of the design)
_UNSUPPORTED = op.QUANTIFIERS | op.STR_OPERATORS | \
    frozenset([op.STR_CONSTANT, op.ALGEBRAIC_CONSTANT])

_PLAIN = {
    _lib.MSAT_TAG_AND: op.AND,
    _lib.MSAT_TAG_OR: op.OR,
    _lib.MSAT_TAG_NOT: op.NOT,
    _lib.MSAT_TAG_IFF: op.IFF,
    _lib.MSAT_TAG_ITE: op.ITE,
    _lib.MSAT_TAG_EQ: op.EQUALS,
    _lib.MSAT_TAG_LEQ: op.LE,
    _lib.MSAT_TAG_PLUS: op.PLUS,
    _lib.MSAT_TAG_TIMES: op.TIMES,
    _lib.MSAT_TAG_DIVIDE: op.DIV,
    _lib.MSAT_TAG_FLOOR: op.TOINT,
    _lib.MSAT_TAG_INT_FROM_UBV: op.BV_TONATURAL,
    _lib.MSAT_TAG_ARRAY_READ: op.ARRAY_SELECT,
    _lib.MSAT_TAG_ARRAY_WRITE: op.ARRAY_STORE,
    _lib.MSAT_TAG_BV_ULT: op.BV_ULT,
    _lib.MSAT_TAG_BV_SLT: op.BV_SLT,
    _lib.MSAT_TAG_BV_ULE: op.BV_ULE,
    _lib.MSAT_TAG_BV_SLE: op.BV_SLE,
}

# BV operators whose payload is (width,)
_BV_WIDTH = {
    _lib.MSAT_TAG_BV_MUL: op.BV_MUL,
    _lib.MSAT_TAG_BV_ADD: op.BV_ADD,
    _lib.MSAT_TAG_BV_SUB: op.BV_SUB,
    _lib.MSAT_TAG_BV_NEG: op.BV_NEG,
    _lib.MSAT_TAG_BV_UDIV: op.BV_UDIV,
    _lib.MSAT_TAG_BV_UREM: op.BV_UREM,
    _lib.MSAT_TAG_BV_SDIV: op.BV_SDIV,
    _lib.MSAT_TAG_BV_SREM: op.BV_SREM,
    _lib.MSAT_TAG_BV_CONCAT: op.BV_CONCAT,
    _lib.MSAT_TAG_BV_OR: op.BV_OR,
    _lib.MSAT_TAG_BV_XOR: op.BV_XOR,
    _lib.MSAT_TAG_BV_AND: op.BV_AND,
    _lib.MSAT_TAG_BV_NOT: op.BV_NOT,
    _lib.MSAT_TAG_BV_LSHL: op.BV_LSHL,
    _lib.MSAT_TAG_BV_LSHR: op.BV_LSHR,
    _lib.MSAT_TAG_BV_ASHR: op.BV_ASHR,
    _lib.MSAT_TAG_BV_COMP: op.BV_COMP,
}

# BV operators whose payload is (width, amount), with the msat_term_is_* getter
_BV_AMOUNT = {
    _lib.MSAT_TAG_BV_ZEXT: (op.BV_ZEXT, _lib.msat_term_is_bv_zext),
    _lib.MSAT_TAG_BV_SEXT: (op.BV_SEXT, _lib.msat_term_is_bv_sext),
    _lib.MSAT_TAG_BV_ROL: (op.BV_ROL, _lib.msat_term_is_bv_rol),
    _lib.MSAT_TAG_BV_ROR: (op.BV_ROR, _lib.msat_term_is_bv_ror),
}


class MSatFNode(FNode):
    """An FNode whose only state is a MathSAT term (or decl).

    Function symbols have no MathSAT term, so they hold the msat_decl
    and _term is None. MathSAT folds ToReal(i) into i, so _as_real marks
    the Real view of an Int-sorted term (ToReal(i), Real(0)).
    """
    __slots__ = ["_mgr", "_term", "_decl", "_as_real", "_cache"]

    def __init__(self, mgr: "MSatFormulaManager", term: Any, decl: Any,
                 node_id: int, as_real: bool=False):
        # FNode.__init__ is skipped: _content is computed, not stored
        self._mgr = mgr
        self._term = term
        self._decl = decl
        self._as_real = as_real
        self._cache: Optional[FNodeContent] = None
        self._node_id = node_id

    @property # type: ignore[override]
    def _content(self) -> FNodeContent:
        if self._cache is None:
            self._cache = self._mgr._decode(self)
        return self._cache


class MSatFormulaManager(FormulaManager):
    """FormulaManager that builds every node as a MathSAT term."""

    def __init__(self, env):
        # Root env: every native term lives here, solvers use siblings
        self.msat_root = MSatEnv()
        self._nodes: Dict[Tuple[str, int], MSatFNode] = {}
        self._builder_conv: Optional[MSatConverter] = None
        FormulaManager.__init__(self, env)

    @property
    def _builder(self) -> MSatConverter:
        # Lazy: the Environment creates its TypeManager after us
        if self._builder_conv is None:
            self._builder_conv = MSatConverter(self.env, self.msat_root)
        return self._builder_conv

    def __contains__(self, node: FNode) -> bool:
        return isinstance(node, MSatFNode) and node._mgr is self

    #
    # Construction
    #
    def create_node(self, node_type: int, args: Tuple[FNode, ...], payload: Optional[Any]=None) -> FNode:
        if node_type in _UNSUPPORTED or node_type in op.CUSTOM_NODE_TYPES:
            raise NotImplementedError("MathSAT native nodes do not support %s"
                                      % op.op_to_str(node_type))
        if node_type == op.POW and not args[1].is_constant():
            raise NotImplementedError("MathSAT native nodes do not support "
                                      "non-constant exponents")
        if node_type == op.SYMBOL:
            return self._make_symbol(*payload)

        tmp = FNode(FNodeContent(node_type, args, payload), -1)
        ty, arg_types = self._check_type(tmp, args)
        e = self.msat_root()
        terms = [a._term for a in args] # type: ignore[attr-defined]
        if node_type == op.FUNCTION:
            if any(t.is_bool_type() for t in arg_types):
                raise NotImplementedError("MathSAT does not support UF with "
                                          "Bool arguments")
            term = _lib.msat_make_uf(e, payload._decl, terms)
        elif node_type == op.BOOL_CONSTANT:
            term = _lib.msat_make_true(e) if payload else _lib.msat_make_false(e)
        else:
            # Some walk_* ask the type checker about tmp: answer from ty
            stc = self.env.stc
            stc.memoization[tmp] = ty
            try:
                term = MSatConverter.super(self._builder, tmp, args=terms)
            finally:
                del stc.memoization[tmp]
        if _lib.MSAT_ERROR_TERM(term):
            raise PysmtTypeError(_lib.msat_last_error_message(e))
        return self._wrap(term, as_real=(ty == types.REAL and self._is_int(term)))

    def _check_type(self, tmp: FNode, args: Tuple[FNode, ...]):
        """Type-checks one level of tmp, without memoizing tmp."""
        stc = self.env.stc
        arg_types = [stc.get_type(a) for a in args]
        ty = type(stc).super(stc, tmp, args=arg_types)
        if ty is None:
            raise PysmtTypeError("%s is not well-typed on arguments of type %s"
                                 % (op.op_to_str(tmp.node_type()),
                                    ", ".join(str(t) for t in arg_types)))
        return ty, arg_types

    def _make_symbol(self, name: str, typename: types.PySMTType) -> FNode:
        if typename.is_function_type() and \
           any(t.is_bool_type() for t in typename.param_types): # type: ignore[attr-defined]
            # msat_get_function_type segfaults on Bool parameters
            raise NotImplementedError("MathSAT does not support UF with "
                                      "Bool arguments")
        b = self._builder
        e = self.msat_root()
        decl = _lib.msat_declare_function(e, b._rename_empty(name),
                                          b._type_to_msat(typename))
        if _lib.MSAT_ERROR_DECL(decl):
            raise PysmtTypeError(_lib.msat_last_error_message(e))
        if typename.is_function_type():
            return self._wrap_decl(decl, typename)
        return self._wrap(_lib.msat_make_constant(e, decl))

    #
    # Identity
    #
    def _wrap(self, term: Any, as_real: bool=False) -> MSatFNode:
        tid = _lib.msat_term_id(term)
        key = ("r" if as_real else "t", tid)
        n = self._nodes.get(key)
        if n is None:
            decl = _lib.msat_term_get_decl(term)
            if _lib.msat_decl_get_arity(decl) > _lib.msat_term_arity(term):
                # A function symbol (e.g., from a model) is its decl
                return self._wrap_decl(decl)
            # Two node ids per term: the natural view and the Real view
            n = MSatFNode(self, term, None, 2 * tid + int(as_real), as_real)
            self._nodes[key] = n
            self.env.stc.memoization[n] = types.REAL if as_real else \
                self._to_type(_lib.msat_term_get_type(term))
        return n

    def _is_int(self, term: Any) -> bool:
        return bool(_lib.msat_is_integer_type(self.msat_root(),
                                              _lib.msat_term_get_type(term)))

    def _wrap_decl(self, decl: Any, typename: Optional[types.PySMTType]=None) -> MSatFNode:
        did = _lib.msat_decl_id(decl)
        n = self._nodes.get(("d", did))
        if n is None:
            if typename is None:
                params = [self._to_type(_lib.msat_decl_get_arg_type(decl, i))
                          for i in range(_lib.msat_decl_get_arity(decl))]
                ret = self._to_type(_lib.msat_decl_get_return_type(decl))
                typename = self.env.type_manager.FunctionType(ret, params)
            # Negative ids keep decl ids apart from term ids
            n = MSatFNode(self, None, decl, -(did + 1))
            self._nodes[("d", did)] = n
            self.env.stc.memoization[n] = typename
        return n

    def _to_type(self, msat_type: Any) -> types.PySMTType:
        # Bool shortcut: TRUE/FALSE are built before the TypeManager exists
        e = self.msat_root()
        if _lib.msat_is_bool_type(e, msat_type):
            return types.BOOL
        try:
            return self._builder._msat_type_to_type(msat_type)
        except NotImplementedError:
            # Int and Real are simple types too, so custom sorts are tried last
            is_simple, name = _lib.msat_is_simple_type(e, msat_type)
            if not is_simple:
                raise
            return self.env.type_manager.Type(name)

    #
    # Decoding
    #
    def _decode(self, n: MSatFNode) -> FNodeContent:
        e = self.msat_root()
        b = self._builder
        get_type = self.env.stc.get_type
        if n._term is None:
            name = b._restore_empty(_lib.msat_decl_get_name(n._decl))
            return FNodeContent(op.SYMBOL, (), (name, get_type(n)))

        t = n._term
        if n._as_real:
            if _lib.msat_term_is_number(e, t):
                _, value = b._number_payload(t)
                return FNodeContent(op.REAL_CONSTANT, (), Fraction(value))
            return FNodeContent(op.TOREAL, (self._wrap(t),), None)

        decl = _lib.msat_term_get_decl(t)
        tag = _lib.msat_decl_get_tag(e, decl)
        args = tuple(self._wrap_arg(t, decl, i)
                     for i in range(_lib.msat_term_arity(t)))
        if tag == _lib.MSAT_TAG_TRUE:
            return FNodeContent(op.BOOL_CONSTANT, (), True)
        if tag == _lib.MSAT_TAG_FALSE:
            return FNodeContent(op.BOOL_CONSTANT, (), False)
        if tag in _PLAIN:
            return FNodeContent(_PLAIN[tag], args, None)
        if tag in _BV_WIDTH:
            return FNodeContent(_BV_WIDTH[tag], args, (self._width(t),))
        if tag in _BV_AMOUNT:
            node_type, getter = _BV_AMOUNT[tag]
            _, amount = getter(e, t)
            return FNodeContent(node_type, args, (self._width(t), amount))
        if tag == _lib.MSAT_TAG_BV_EXTRACT:
            _, msb, lsb = _lib.msat_term_is_bv_extract(e, t)
            return FNodeContent(op.BV_EXTRACT, args, (msb - lsb + 1, lsb, msb))
        if tag == _lib.MSAT_TAG_ARRAY_CONST:
            idx_type = get_type(n).index_type # type: ignore[attr-defined]
            return FNodeContent(op.ARRAY_VALUE, args, idx_type)
        if tag == _lib.MSAT_TAG_UNKNOWN:
            if _lib.msat_term_is_number(e, t):
                node_type, value = b._number_payload(t)
                if node_type == op.INT_CONSTANT:
                    value = pysmt_integer_from_integer(value)
                return FNodeContent(node_type, (), value)
            if _lib.msat_term_is_constant(e, t):
                name = b._restore_empty(_lib.msat_decl_get_name(decl))
                return FNodeContent(op.SYMBOL, (), (name, get_type(n)))
            if _lib.msat_term_is_uf(e, t):
                return FNodeContent(op.FUNCTION, args, self._wrap_decl(decl))
        raise ConvertExpressionError("Unsupported MathSAT term: %s"
                                     % _lib.msat_term_repr(t))

    def _wrap_arg(self, term: Any, decl: Any, i: int) -> MSatFNode:
        """Wraps the i-th argument, as Real where MathSAT coerced it."""
        arg = _lib.msat_term_get_arg(term, i)
        as_real = self._is_int(arg) and i < _lib.msat_decl_get_arity(decl) and \
            _lib.msat_is_rational_type(self.msat_root(),
                                       _lib.msat_decl_get_arg_type(decl, i))
        return self._wrap(arg, as_real=bool(as_real))

    def _width(self, term: Any) -> int:
        _, width = _lib.msat_is_bv_type(self.msat_root(), _lib.msat_term_get_type(term))
        return width


class NativeMSatConverter(MSatConverter):
    """Converter for solvers in a native MathSAT environment.

    The solver env is a sibling of the manager's root env, so native
    terms are valid in it as they are.
    """

    def convert(self, formula: FNode) -> Any:
        if formula not in self.mgr:
            raise PysmtTypeError("%s does not belong to this native "
                                 "environment" % formula)
        if formula._term is None: # type: ignore[attr-defined]
            raise InternalSolverError("Function symbols have no MathSAT term")
        return formula._term # type: ignore[attr-defined]

    def back(self, expr: Any) -> FNode:
        return self.mgr._wrap(expr)
