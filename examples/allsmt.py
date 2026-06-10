# This example requires MathSAT to be installed.
from pysmt.shortcuts import LE, GE, Int, Plus, Equals, Solver, And, Symbol, Or, get_atoms
from pysmt.typing import INT


def callback(model, converter, result):
    """Callback for msat.all_sat.

    This function is called by the MathSAT API everytime a new model
    is found. If the function returns 1, the search continues,
    otherwise it stops.
    """
    # Elements in model are msat_term .
    # Converter.back() provides the pySMT representation of a solver term.
    py_model = [converter.back(v) for v in model]
    result.append(And(py_model))
    return 1  # go on


def all_smt(formula, important):
    result = []
    with Solver(name="msat",
                solver_options={
                    "dpll.allsat_minimize_model": "false",  # enumerate total models
                    "dpll.allsat_allow_duplicates": "false",  # enumerate disjoint models
                    "preprocessor.toplevel_propagation": "false",  # these two options are necessary
                    "preprocessor.simplification": "0",  # to avoid non-validity-preserving simplifications
                }
                ) as msat:
        msat.add_assertion(formula)
        msat.all_sat(important, lambda model: callback(model, msat.converter, result))
    return result


A0 = Symbol("A0", INT)
A1 = Symbol("A1", INT)
x = Symbol("x")
y = Symbol("y")

f = And(GE(A0, Int(0)), LE(A0, Int(5)),
        GE(A1, Int(0)), LE(A1, Int(5)),
        Equals(Plus(A0, A1), Int(8)),
        Or(x, y))

important = get_atoms(f) - {y}
result = all_smt(f, important)

print("'exists y . %s'\nis equivalent to\n'%s'" % (f, Or(result).serialize()))
