# This example requires MathSAT to be installed.
#
# This example shows how to use a solver converter to access
# functionalities of the solver that are not wrapped by pySMT.
#
# Our goal is to call the method msat_all_sat from the MathSAT API.
#
import mathsat
from pysmt.shortcuts import Or, Symbol, Solver, And

def callback(model, converter, result):
    """Callback for msat_all_sat.

    This function is called by the MathSAT API everytime a new model
    is found. If the function returns 1, the search continues,
    otherwise it stops.
    """
    # Elements in model are msat_term .
    # Converter.back() provides the pySMT representation of a solver term.
    py_model = [converter.back(v) for v in model]
    result.append(And(py_model))
    return 1 # go on

x, y = Symbol("x"), Symbol("y")
f = Or(x, y)

msat = Solver(name="msat")
converter = msat.converter # .converter is a property implemented by all solvers
msat.add_assertion(f) # This is still at pySMT level

result = []
# Directly invoke the mathsat API !!!
# The second term is a list of "important variables"
mathsat.msat_all_sat(msat.msat_env(),
      [converter.convert(x)],      # Convert the pySMT term into a MathSAT term
      lambda model : callback(model, converter, result))

print("'exists y . %s' is equivalent to '%s'" %(f, Or(result)))
#exists y . (x | y) is equivalent to ((! x) | x)
