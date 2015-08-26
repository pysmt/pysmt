# Perform ALL-SMT on Theory atoms
#
# This example shows:
#  - How to get the logic of a formula
#  - How to enumerate models
#  - How to extract a partial model
#  - How to use the special operator EqualsOrIff
#
from pysmt.shortcuts import Solver, Not, And, Symbol, Or
from pysmt.shortcuts import LE, GE, Int, Plus, Equals, EqualsOrIff
from pysmt.typing import INT
from pysmt.oracles import get_logic

def all_smt(formula, keys):
    target_logic = get_logic(formula)
    print("Target Logic: %s" % target_logic)
    with Solver(logic=target_logic) as solver:
        solver.add_assertion(formula)
        while solver.solve():
            partial_model = [EqualsOrIff(k, solver.get_value(k)) for k in keys]
            print(partial_model)
            solver.add_assertion(Not(And(partial_model)))


A0 = Symbol("A0", INT)
A1 = Symbol("A1", INT)
A2 = Symbol("A2", INT)

f = And(GE(A0, Int(0)), LE(A0, Int(5)),
        GE(A1, Int(0)), LE(A1, Int(5)),
        GE(A2, Int(0)), LE(A2, Int(5)),
        Equals(Plus(A0, A1, A2), Int(8)))

all_smt(f, [A0, A1, A2])

# By using the operator EqualsOrIff, we can mix theory and bool variables
x = Symbol("x")
y = Symbol("y")
f = And(f, Or(x,y))

all_smt(f, [A0, A1, A2, x])
