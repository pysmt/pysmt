# This example requires Z3
#
# This example shows how to parallelize solving using pySMT, by using
# the multiprocessing library.
#
# All shortcuts (is_sat, is_unsat, get_model, etc.) can be easily
# used. We sho two techniques: map and apply_async.
#
# Map applies a given function to a list of elements, and returns a
# list of results. We show an example using is_sat.
#
# Apply_async provides a way to perform operations in an asynchronous
# way. This allows us to start multiple solving processes in parallel,
# and collect the results whenever they become available.
#
# More information can be found in the Python Standard Library
# documentation for the multiprocessing module.
#
#
# NOTE: When running this example, a warning will appear saying:
#   "Contextualizing formula during is_sat"
#
# Each process will inherit a different formula manager, but the
# formulas that we are solving have been all created in the same
# formula manager. pySMT takes care of moving the formula across
# formula managers. This step is called contextualization, and occurs
# only when using multiprocessing.
# To disable the warning see the python module warnings.
#
from multiprocessing import Pool, TimeoutError
from time import sleep

from pysmt.test.examples import get_example_formulae
from pysmt.shortcuts import is_sat, is_valid, is_unsat
from pysmt.shortcuts import And

# Ignore this for now
def check_validity_and_test(args):
    """Checks expression and compare the outcome against a known value."""

    expr, expected = args # IMPORTANT: Unpack args !!!
    local_res = is_valid(expr)
    return local_res == expected


# Create the Pool with 4 workers.
pool = Pool(4)

# We use the examples formula from the test suite.
# This generator iterates over all the expressions
f_gen = (f.expr for f in get_example_formulae())

# Call the functino is_sat on each expression
res = pool.map(is_sat, f_gen)

# The result is a list of True/False, in the same order as the input.
print(res)

sleep(1) # Have some time to look at the result

# Notice that all shortcuts (is_sat, qelim, etc) require only one
# mandatory argument. To pass multiple arguments, we need to pack them
# together.

# Lets create a list of (formula, result), where result is the
# expected result of the is_valid query.
f_gen = (f.expr for f in get_example_formulae())
res_gen = (f.is_valid for f in get_example_formulae())
args_gen = zip(f_gen, res_gen)

# We now define a function that check the formula against the expected
# value of is_valid: See check_validity_and_test(...) above.
# Due to the way multiprocessing works, we need to define the function
# _before_ we create the Pool.

# As before, we call the map on the pool
res = pool.map(check_validity_and_test, args_gen)

# We can also apply a map-reduce strategy, by making sure that all
# results are as expected.
if all(res):
    print("Everything is ok!")
else:
    print("Ooops, something is wrong!")
    print(res)

# A different option is to run solvers in an asynchronous way.  This
# does not provide us with any guarantee on the execution order, but
# it is particular convenient, if we want to perform solving together
# with another long operation (e.g., I/O, network etc.)  or if we want
# to run multiple solvers.

# Create a formula
big_f = And(f.expr for f in get_example_formulae() \
            if not f.logic.theory.bit_vectors and \
               not f.logic.theory.arrays and \
               not f.logic.theory.strings and \
                   f.logic.theory.linear)

# Create keyword arguments for the function call.
# This is the simplest way to pass multiple arguments to apply_async.
kwargs = {"formula": big_f, "solver_name": "z3"}
future_res_sat = pool.apply_async(is_sat, kwds=kwargs)
future_res_unsat = pool.apply_async(is_unsat, kwds=kwargs)

# In the background, the solving is taking place... We can do other
# stuff in the meanwhile.
print("This is non-blocking...")

# Get the result with a deadline.
# See multiprocessing.pool.AsyncResult for more options
sat_res = future_res_sat.get(10)  # Get result after 10 seconds or kill
try:
    unsat_res = future_res_unsat.get(0) # No wait
except TimeoutError:
    print("UNSAT result was not ready!")
    unsat_res = None
print(sat_res, unsat_res)
