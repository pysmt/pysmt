# Linear Temporal Logic
#
# This example shows how to extend pySMT in order to support
# additional operators. This can be achieved without modifying the
# pySMT source code.
#
# We use LTL as an example, and we define some basic operators.
#

# First we need to define the new operators, or "node types"
from pysmt.operators import new_node_type

LTL_X = new_node_type(node_str="LTL_X")
LTL_Y = new_node_type(node_str="LTL_Y")
LTL_Z = new_node_type(node_str="LTL_Z")
LTL_F = new_node_type(node_str="LTL_F")
LTL_G = new_node_type(node_str="LTL_G")
LTL_O = new_node_type(node_str="LTL_O")
LTL_H = new_node_type(node_str="LTL_H")
LTL_U = new_node_type(node_str="LTL_U")
LTL_S = new_node_type(node_str="LTL_S")
ALL_LTL = (LTL_X, LTL_Y, LTL_Z,
           LTL_F, LTL_G, LTL_O, LTL_H,
           LTL_U, LTL_S)

# The FormulaManager needs to be extended to be able to use these
# operators. Notice that additional checks, and some simplifications
# can be performed at construction time. We keep this example simple.
import pysmt.environment
import pysmt.formula

class FormulaManager(pysmt.formula.FormulaManager):
    """Extension of FormulaManager to handle LTL Operators."""
    def X(self, formula):
        return self.create_node(node_type=LTL_X, args=(formula,))

    def Y(self, formula):
        return self.create_node(node_type=LTL_Y, args=(formula,))

    def Z(self, formula):
        return self.create_node(node_type=LTL_Z, args=(formula,))

    def F(self, formula):
        return self.create_node(node_type=LTL_F, args=(formula,))

    def G(self, formula):
        return self.create_node(node_type=LTL_G, args=(formula,))

    def O(self, formula):
        return self.create_node(node_type=LTL_O, args=(formula,))

    def H(self, formula):
        return self.create_node(node_type=LTL_H, args=(formula,))

    def S(self, left, right):
        return self.create_node(node_type=LTL_S, args=(left, right))

    def U(self, left, right):
        return self.create_node(node_type=LTL_U, args=(left, right))

    # We can also add syntactic sugar, by creating constructors that
    # are not mapped directly to a new node type. For example X^n:
    def Xn(self, n, formula):
        X_ = self.X
        res = formula
        for _ in range(n):
            res = X_(res)
        return res

#
# For the system to work, we need to extend a few walkers.
#

# The first extension is the TypeChecker. The typechecker provides
# several convenience methods for many types of operators. In this
# case, all the LTL operators have boolean argument and boolean return
# value, therefore we map them all to walk_bool_to_bool.
#
# This is an example of how to extend an existing class
# (SimpleTypeChecker) in order to deal with new node-types, by calling
# an existing method (walk_bool_to_bool).
from pysmt.type_checker import SimpleTypeChecker
SimpleTypeChecker.set_handler(SimpleTypeChecker.walk_bool_to_bool, *ALL_LTL)

from pysmt.oracles import FreeVarsOracle
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, *ALL_LTL)

# An alternative approach is to subclass the walker that we are
# interested in. For example, the HRPrinter has utility methods for
# the nary operators. For the unary operators, we define a unique
# function.  The walk_* method that we override needs to have the same
# name as the string used in new_node_type (lowercase): for LTL_G, we
# override walk_ltl_g.

import pysmt.printers
from pysmt.walkers.generic import handles
LTL_TYPE_TO_STR = { LTL_X: "X", LTL_Y: "Y", LTL_Z: "Z",
                    LTL_F: "F", LTL_G: "F", LTL_O: "O", LTL_H: "H"}

class HRPrinter(pysmt.printers.HRPrinter):
    def walk_ltl_s(self, formula):
        return self.walk_nary(formula, " S ")

    def walk_ltl_u(self, formula):
        return self.walk_nary(formula, " U ")

    @handles(LTL_X, LTL_Y, LTL_Z, LTL_F, LTL_G, LTL_O, LTL_H)
    def walk_ltl(self, formula):
        node_type = formula.node_type()
        op_symbol = LTL_TYPE_TO_STR[node_type]
        self.stream.write("(%s " % op_symbol)
        yield formula.arg(0)
        self.stream.write(")")

# EOC HRPrinter

class HRSerializer(pysmt.printers.HRSerializer):
    PrinterClass = HRPrinter

# EOC HRSerialize

# Finally, a third option is to define new methods and attach them to
# existing classes. We do so for the IdentityDagWalker
from pysmt.walkers import IdentityDagWalker

def walk_ltl_x(self, formula, args, **kwargs): return self.mgr.X(args[0])
def walk_ltl_y(self, formula, args, **kwargs): return self.mgr.Y(args[0])
def walk_ltl_u(self, formula, args, **kwargs): return self.mgr.U(args[0], args[1])
def walk_ltl_s(self, formula, args, **kwargs): return self.mgr.S(args[0], args[1])
def walk_ltl_f(self, formula, args, **kwargs): return self.mgr.F(args[0])
def walk_ltl_g(self, formula, args, **kwargs): return self.mgr.G(args[0])
def walk_ltl_o(self, formula, args, **kwargs): return self.mgr.O(args[0])
def walk_ltl_h(self, formula, args, **kwargs): return self.mgr.H(args[0])

IdentityDagWalker.set_handler(walk_ltl_x, LTL_X)
IdentityDagWalker.set_handler(walk_ltl_y, LTL_Y)
IdentityDagWalker.set_handler(walk_ltl_u, LTL_U)
IdentityDagWalker.set_handler(walk_ltl_s, LTL_S)
IdentityDagWalker.set_handler(walk_ltl_f, LTL_F)
IdentityDagWalker.set_handler(walk_ltl_g, LTL_G)
IdentityDagWalker.set_handler(walk_ltl_o, LTL_O)
IdentityDagWalker.set_handler(walk_ltl_h, LTL_H)
# EOC IdentityDagWalker

from pysmt.environment import Environment, pop_env, get_env
from pysmt.environment import push_env as pysmt_push_env

class EnvironmentLTL(Environment):
    """Extension of pySMT environment."""
    # Only specify new classes. Classes that have been extended
    # directly do not need to be redefined here (e.g., TypeChecker)
    FormulaManagerClass = FormulaManager
    HRSerializerClass = HRSerializer

# EOC EnvironmentLTL


def push_env(env=None):
    """Overload push_env to default to the new Environment class."""
    if env is None:
        env = EnvironmentLTL()
    return pysmt_push_env(env=env)

def reset_env():
    """Overload reset_env to use the new push_env()."""
    pop_env()
    push_env()
    return get_env()

# Create the default environment
reset_env()


if __name__ == "__main__":
    with EnvironmentLTL() as env:
        mgr = env.formula_manager
        f = mgr.X(mgr.Symbol("x"))
        g = mgr.G(f)
        print(g)
        print(g.get_free_variables())
