# This example requires MathSAT to be installed.

from pysmt.shortcuts import And, Or, Solver, Symbol


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


x, y = Symbol("x"), Symbol("y")
f = Or(x, y)

result = []
with Solver(name="msat") as msat:
    converter = msat.converter  # .converter is a property implemented by all solvers
    msat.add_assertion(f)
    msat.all_sat([x], lambda model: callback(model, converter, result))

    print("'exists y . %s' is equivalent to '%s'" % (f, Or(result)))
    # exists y . (x | y) is equivalent to ((! x) | x)
