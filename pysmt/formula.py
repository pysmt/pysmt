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
"""The FormulaManager is used to create formulae.

All objects are memoized so that two syntactically equivalent formulae
are represented by the same object.

The FormulaManager provides many more constructors than the operators
defined (operators.py). This is because many operators are rewritten,
and therefore are only virtual. Common examples are GE, GT that are
rewritten as LE and LT. Similarly, the operator Xor is rewritten using
its definition.
"""

import collections

from fractions import Fraction

import pysmt.typing as types
import pysmt.operators as op

from pysmt.fnode import FNode, FNodeContent
from pysmt.exceptions import NonLinearError
from pysmt.walkers.identitydag import IdentityDagWalker

class FormulaManager(object):
    """FormulaManager is responsible for the creation of all formulae."""

    def __init__(self, env=None):
        self.env = env
        # Attributes for handling symbols and formulae
        self.formulae = {}
        self.symbols = {}
        self._fresh_guess = 0
        # get_type() from TypeChecker will be initialized lazily
        self.get_type = None

        self.int_constants = {}
        self.real_constants = {}
        self.true_formula = self.create_node(node_type=op.BOOL_CONSTANT,
                                             args=tuple(),
                                             payload=True)
        self.false_formula = self.create_node(node_type=op.BOOL_CONSTANT,
                                              args=tuple(),
                                              payload=False)
        return

    def _do_type_check_real(self, formula):
        self.get_type(formula)

    def _do_type_check(self, formula):
        self.get_type = self.env.stc.get_type
        self._do_type_check = self._do_type_check_real
        return self._do_type_check(formula)

    def create_node(self, node_type, args, payload=None):
        content = FNodeContent(node_type, args, payload)
        if content in self.formulae:
            return self.formulae[content]
        else:
            n = FNode(content)
            self.formulae[content] = n
            self._do_type_check(n)
            return n

    def _create_symbol(self, name, typename=types.BOOL):
        assert name not in self.symbols
        n = self.create_node(node_type=op.SYMBOL,
                             args=tuple(),
                             payload=(name, typename))
        self.symbols[name] = n
        return n

    def new_fresh_symbol(self, typename, base="FV%d"):
        count = self._fresh_guess
        while (base % count) in self.symbols:
            count = count + 1

        name = (base % count)
        self._fresh_guess = count + 1
        v = self.Symbol(name, typename)
        assert v is not None
        return v

    def get_symbol(self, name):
        if name in self.symbols:
            return self.symbols[name]
        return None

    def get_all_symbols(self):
        return self.symbols.values()

    def get_or_create_symbol(self, name, typename):
        s = self.get_symbol(name)
        if s is None:
            s = self._create_symbol(name, typename)
        else:
            if not s.symbol_type() == typename:
                raise TypeError("%s != %s" % (s.symbol_type(), typename))
        return s

    # Node definitions start here

    def Symbol(self, name, typename=types.BOOL):
        v = self.get_or_create_symbol(name, typename)
        return v

    def FreshSymbol(self, typename=types.BOOL, template=None):
        if template is None:
            return self.new_fresh_symbol(typename)
        else:
            return self.new_fresh_symbol(typename, template)


    def ForAll(self, variables, formula):
        """ Creates an expression of the form:
            Forall variables. formula(variables)

        Restrictions:
         - Formula must be of boolean type
         - Variables must be BOOL, REAL or INT
        """
        if len(variables) > 0:
            n = self.create_node(node_type=op.FORALL,
                                 args=(formula,),
                                 payload=tuple(variables))
            return n
        else:
            return formula


    def Exists(self, variables, formula):
        """ Creates an expression of the form:
            Exists variables. formula(variables)

        Restrictions:
         - Formula must be of boolean type
         - Variables must be BOOL, REAL or INT
        """
        if len(variables) > 0:
            n = self.create_node(node_type=op.EXISTS,
                                 args=(formula,),
                                 payload=tuple(variables))
            return n
        else:
            return formula


    def Function(self, vname, params):
        assert len(params) == len(vname.symbol_type().param_types)
        n = self.create_node(node_type=op.FUNCTION,
                             args=tuple(params),
                             payload=vname)
        return n


    def Not(self, formula):
        """ Creates an expression of the form:
            not formula

        Restriction: Formula must be of boolean type
        """
        n = self.create_node(node_type=op.NOT, args=(formula,))
        return n


    def Implies(self, left, right):
        """ Creates an expression of the form:
            left -> right

        Restriction: Left and Right must be of boolean type
        """
        n = self.create_node(node_type=op.IMPLIES, args=(left, right))
        return n


    def Iff(self, left, right):
        """ Creates an expression of the form:
            left <-> right

        Restriction: Left and Right must be of boolean type
        """
        n = self.create_node(node_type=op.IFF, args=(left, right))
        return n


    def Minus(self, left, right):
        """ Creates an expression of the form:
            left - right

        Restriction: Left and Right must be both INT or REAL type
        """
        n = self.create_node(node_type=op.MINUS, args=(left, right))
        return n


    def Times(self, left, right):
        """ Creates an expression of the form:
            left * right

        Restriction:
          - Left and Right must be both INT or REAL type
          - Only linear expressions are allowed
        """
        n = self.create_node(node_type=op.TIMES, args=(left, right))
        return n


    def Div(self, left, right):
        """ Creates an expression of the form:
            left / right

        Restriction:
          - Left and Right must be both REAL type
          - Right is a constant
        """
        if not right.is_constant(types.REAL):
            raise NonLinearError
        inverse = Fraction(1) / right.constant_value()
        return self.Times(left, self.Real(inverse))


    def Equals(self, left, right):
        """ Creates an expression of the form:
            left = right

        Restriction: Left and Right must be both REAL or INT type
        """
        n = self.create_node(node_type=op.EQUALS, args=(left, right))
        return n


    def GE(self, left, right):
        """ Creates an expression of the form:
            left >= right

        Restriction: Left and Right must be both REAL or INT type
        """
        n = self.create_node(node_type=op.LE, args=(right, left))
        return n


    def GT(self, left, right):
        """ Creates an expression of the form:
            left > right

        Restriction: Left and Right must be both REAL or INT type
        """
        n = self.create_node(node_type=op.LT, args=(right, left))
        return n


    def LE(self, left, right):
        """ Creates an expression of the form:
            left <= right

        Restriction: Left and Right must be both REAL or INT type
        """
        n = self.create_node(node_type=op.LE, args=(left, right))
        return n


    def LT(self, left, right):
        """ Creates an expression of the form:
            left < right

        Restriction: Left and Right must be both REAL or INT type
        """
        n = self.create_node(node_type=op.LT, args=(left, right))
        return n


    def Ite(self, iff, left, right):
        """ Creates an expression of the form:
            if( iff ) then  left  else  right

        Restriction:
          - Iff must be BOOL
          - Left and Right must be both of the same type
        """
        n = self.create_node(node_type=op.ITE, args=(iff, left, right))
        return n


    def Real(self, value):
        """ Returns a Real-type constant of the given value.

        value can be:
          - A Fraction(n,d)
          - A tuple (n,d)
          - A long or int n
          - A float
        """
        if value in self.real_constants:
            return self.real_constants[value]

        if type(value) == Fraction:
            val = value
        elif type(value) == tuple:
            val = Fraction(value[0], value[1])
        elif type(value) == long or type(value) == int:
            val = Fraction(value, 1)
        elif type(value) == float:
            val = Fraction.from_float(value)
        else:
            raise TypeError("Invalid type in constant. The type was:" + \
                            str(type(value)))

        n = self.create_node(node_type=op.REAL_CONSTANT,
                             args=tuple(),
                             payload=val)
        self.real_constants[value] = n
        return n

    def Int(self, value):
        """Return a constant of type INT."""
        if value in self.int_constants:
            return self.int_constants[value]

        if type(value) == long or type(value) == int:
            n = self.create_node(node_type=op.INT_CONSTANT,
                                 args=tuple(),
                                 payload=value)
            self.int_constants[value] = n
            return n
        else:
            raise TypeError("Invalid type in constant. The type was:" + \
                            str(type(value)))

    def TRUE(self):
        """Return the boolean constant True."""
        return self.true_formula

    def FALSE(self):
        """Return the boolean constant False."""
        return self.false_formula

    def Bool(self, value):
        if type(value) != bool:
            raise TypeError("Expecting bool, got %s" % type(value))

        if value:
            return self.true_formula
        else:
            return self.false_formula


    def And(self, *args):
        """ Returns a conjunction of terms.

        This function has polimorphic arguments:
          - And(a,b,c)
          - And([a,b,c])

        Restriction: Arguments must be boolean
        """
        tuple_args = self._polymorph_args_to_tuple(args)

        if len(tuple_args) == 0:
            n = self.TRUE()
        elif len(tuple_args) == 1:
            n = tuple_args[0]
        else:
            n = self.create_node(node_type=op.AND,
                                 args=tuple_args)
        return n


    def Or(self, *args):
        """ Returns an disjunction of terms.

        This function has polimorphic n-arguments:
          - Or(a,b,c)
          - Or([a,b,c])

        Restriction: Arguments must be boolean
        """
        tuple_args = self._polymorph_args_to_tuple(args)

        if len(tuple_args) == 0:
            n = self.FALSE()
        elif len(tuple_args) == 1:
            n = tuple_args[0]
        else:
            n = self.create_node(node_type=op.OR,
                                 args=tuple_args)
        return n


    def Plus(self, *args):
        """ Returns an sum of terms.

        This function has polimorphic n-arguments:
          - Plus(a,b,c)
          - Plus([a,b,c])

        Restriction:
         - Arguments must be all of the same type
         - Arguments must be INT or REAL
        """
        tuple_args = self._polymorph_args_to_tuple(args)
        if len(tuple_args) == 0:
            raise TypeError("Cannot create a Plus without arguments.")

        if len(tuple_args) == 1:
            n = tuple_args[0]
        else:
            n = self.create_node(node_type=op.PLUS,
                                 args=tuple_args)
        return n

    def ToReal(self, formula):
        """ Cast a formula to real type. """
        t = self.env.stc.get_type(formula)
        if t == types.REAL:
            # Ignore casting of a Real
            return formula
        elif t == types.INT:
            return self.create_node(node_type=op.TOREAL,
                                    args=(formula,))
        else:
            raise TypeError("Argument is of type %s, but INT was expected!\n" % t)


    def AtMostOne(self, bool_exprs):
        """ At most one of the bool expressions can be true at anytime.

        This using a quadratic encoding:
           A -> !(B \/ C)
           B -> !(C)
        """
        constraints = []
        for (i, elem) in enumerate(bool_exprs[:-1], start=1):
            constraints.append(self.Implies(elem,
                                            self.Not(self.Or(bool_exprs[i:]))))
        return self.And(constraints)


    def ExactlyOne(self, bool_exprs):
        """ Encodes an exactly-one constraint on the boolean symbols.

        This using a quadratic encoding:
           A \/ B \/ C
           A -> !(B \/ C)
           B -> !(C)
        """
        return self.And(self.Or(bool_exprs),
                        self.AtMostOne(bool_exprs))


    def Xor(self, left, right):
        """Returns the xor of left and right: left XOR right """
        return self.Not(self.Iff(left, right))


    def normalize(self, formula):
        """ Returns the formula normalized to the current Formula Manager.

        This method is useful to contextualize a formula coming from another
        formula manager.
        E.g., f_a is defined with the FormulaManager a, and we want to obtain f_b
              that is the formula f_a expressed on the FormulaManager b :
               f_b = b.normalize(f_a)
        """
        # TODO: name clash with formula normalization
        # TODO: Move this out of the manager and into ad-hoc function
        normalizer = IdentityDagWalker(self.env)
        return normalizer.walk(formula)

    def _polymorph_args_to_tuple(self, args):
        """ Helper function to return a tuple of arguments from args.

        This function is used to allow N-ary operators to express their arguments
        both as a list of arguments or as a tuple of arguments: e.g.,
           And([a,b,c]) and And(a,b,c)
        are both valid, and they are converted into a tuple (a,b,c) """

        if len(args) == 1 and isinstance(args[0], collections.Iterable):
            args = args[0]
        return tuple(args)

    def __contains__(self, node):
        """Checks whether the given node belongs to this formula manager.

        This overloads the 'in' operator, making it possible to write:

           E.g., if x in formula_manager: ...
        """
        if node._content in self.formulae:
            return self.formulae[node._content] == node
        else:
            return False

#EOC FormulaManager

class TypeUnsafeFormulaManager(FormulaManager):
    """Subclass of FormulaManager in which type-checking is disabled.

    TypeUnsafeFormulaManager makes it possible to build expressions
    that are incorrect: e.g., True + 1.  This is used mainly to avoid
    the overhead of having to check each expression for type. For
    example, during parsing we post-pone the type-check after the
    whole expression has been built.

    This should be used with caution.
    """

    def __init__(self, env=None):
        FormulaManager.__init__(self, env)

    def _do_type_check(self, formula):
        pass

    def ToReal(self, formula):
        """ Cast a formula to real type. """
        return self.create_node(node_type=op.TOREAL,
                                args=(formula,))

#EOC TypeUnsafeFormulaManager
