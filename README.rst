===========================
pySMT: a Python API for SMT
===========================

.. image:: https://github.com/pysmt/pysmt/actions/workflows/test.yml/badge.svg
           :target: https://github.com/pysmt/pysmt/actions
           :alt: CI Status

.. image:: https://coveralls.io/repos/github/pysmt/pysmt/badge.svg
           :target: https://coveralls.io/github/pysmt/pysmt
           :alt: Coverage

.. image:: https://readthedocs.org/projects/pysmt/badge/?version=latest
           :target: https://pysmt.readthedocs.io/en/latest/
           :alt: Documentation Status

.. image:: https://img.shields.io/pypi/v/pysmt.svg
           :target: https://pypi.python.org/pypi/pySMT/
           :alt: Latest PyPI version

.. image:: https://img.shields.io/pypi/l/pysmt.svg
           :target: /LICENSE
           :alt: Apache License

.. image:: https://img.shields.io/badge/Browse%20the%20Archive-Google%20groups-orange.svg
           :target: https://groups.google.com/d/forum/pysmt
           :alt: Google groups


pySMT makes working with **Satisfiability Modulo Theory** simple:

* Define formulae in a *simple*, *intuitive*, and *solver independent* way
* Solve your formulae using one of the native solvers, or by wrapping
  any SMT-Lib compliant solver,
* Dump your problems in the SMT-Lib format,
* and more...

.. image:: https://cdn.rawgit.com/pysmt/pysmt/master/docs/architecture.svg
           :alt: PySMT Architecture Overview

Usage
=====

.. code:: python

   >>> from pysmt.shortcuts import Symbol, And, Not, is_sat
   >>>
   >>> varA = Symbol("A") # Default type is Boolean
   >>> varB = Symbol("B")
   >>> f = And(varA, Not(varB))
   >>> f
   (A & (! B))
   >>> is_sat(f)
   True
   >>> g = f.substitute({varB: varA})
   >>> g
   (A & (! A))
   >>> is_sat(g)
   False


A More Complex Example
----------------------

Is there a value for each letter (between 1 and 9) so that H+E+L+L+O = W+O+R+L+D = 25?

.. code:: python

  from pysmt.shortcuts import Symbol, And, GE, LT, Plus, Equals, Int, get_model
  from pysmt.typing import INT

  hello = [Symbol(s, INT) for s in "hello"]
  world = [Symbol(s, INT) for s in "world"]
  letters = set(hello+world)
  domains = And([And(GE(l, Int(1)),
                     LT(l, Int(10))) for l in letters])

  sum_hello = Plus(hello) # n-ary operators can take lists
  sum_world = Plus(world) # as arguments
  problem = And(Equals(sum_hello, sum_world),
                Equals(sum_hello, Int(25)))
  formula = And(domains, problem)

  print("Serialization of the formula:")
  print(formula)

  model = get_model(formula)
  if model:
    print(model)
  else:
    print("No solution found")


Portfolio
---------

Portfolio solving consists of running multiple solvers in
parallel. pySMT provides a simple interface to perform portfolio
solving using multiple solvers and multiple solver configurations.

.. code:: python

   from pysmt.shortcuts import Portfolio, Symbol, Not

   x, y = Symbol("x"), Symbol("y")
   f = x.Implies(y)

   with Portfolio(["cvc4",
                   "yices",
                   ("msat", {"random_seed": 1}),
                   ("msat", {"random_seed": 17}),
                   ("msat", {"random_seed": 42})],
                  logic="QF_UFLIRA",
                  incremental=False,
                  generate_models=False) as s:
     s.add_assertion(f)
     s.push()
     s.add_assertion(x)
     res = s.solve()
     v_y = s.get_value(y)
     print(v_y) # TRUE

     s.pop()
     s.add_assertion(Not(y))
     res = s.solve()
     v_x = s.get_value(x)
     print(v_x) # FALSE


Using other SMT-LIB Solvers
---------------------------

.. code:: python

   from pysmt.shortcuts import Symbol, get_env, Solver
   from pysmt.logics import QF_UFLRA

   name = "mathsat-smtlib" # Note: The API version is called 'msat'

   # Path to the solver. The solver needs to take the smtlib file from
   # stdin. This might require creating a tiny shell script to set the
   # solver options.
   path = ["/tmp/mathsat"]
   logics = [QF_UFLRA,]    # List of the supported logics

   # Add the solver to the environment
   env = get_env()
   env.factory.add_generic_solver(name, path, logics)

   # The solver name of the SMT-LIB solver can be now used anywhere
   # where pySMT would accept an API solver name
   with Solver(name=name, logic="QF_UFLRA") as s:
     print(s.is_sat(Symbol("x"))) # True



Check out more examples in the `examples/ directory
</examples>`_ and the `documentation on ReadTheDocs <http://pysmt.readthedocs.io>`_

Supported Theories and Solvers
==============================

pySMT provides methods to define a formula in Linear Real Arithmetic
(LRA), Real Difference Logic (RDL), Equalities and Uninterpreted
Functions (EUF), Bit-Vectors (BV), Arrays (A), Strings (S) and their
combinations. The following solvers are supported through native APIs:

* MathSAT (http://mathsat.fbk.eu/)
* Z3 (https://github.com/Z3Prover/z3/)
* CVC4 (http://cvc4.cs.nyu.edu/web/)
* Yices 2 (http://yices.csl.sri.com/)
* CUDD (http://vlsi.colorado.edu/~fabio/CUDD/)
* PicoSAT (http://fmv.jku.at/picosat/)
* Boolector (http://fmv.jku.at/boolector/)

Additionally, you can use any SMT-LIB 2 compliant solver.

PySMT assumes that the python bindings for the SMT Solver are
installed and accessible from your ``PYTHONPATH``.

Installation
============
You can install the latest stable release of pySMT from PyPI::

  # pip install pysmt

this will additionally install the *pysmt-install* command, that can
be used to install the solvers: e.g., ::

  $ pysmt-install --check

will show you which solvers have been found in your ``PYTHONPATH``.
PySMT does not depend directly on any solver, but if you want to
perform solving, you need to have at least one solver installed. This
can be used by pySMT via its native API, or passing through an SMT-LIB
file.

The script *pysmt-install* can be used to simplify the installation of the solvers::

 $ pysmt-install --msat

will install MathSAT 5.

By default the solvers are downloaded, unpacked and built in your home directory
in the ``.smt_solvers`` folder. Compiled libraries and actual solver packages are
installed in the relevant ``site-packages`` directory (e.g. virtual environment's
packages root or local user-site). ``pysmt-install`` has many options to
customize its behavior. If you have multiple versions of python in your system,
we recommend the following syntax to run pysmt-install: ``python -m pysmt install``.


*Note:* This script does not install required
dependencies for building the solver (e.g., make or gcc) and has been
tested mainly on Linux Debian/Ubuntu systems. We suggest that you
refer to the documentation of each solver to understand how to install
it with its python bindings.

For Yices, picosat, and CUDD, we use external wrappers:

- yicespy (https://github.com/pysmt/yicespy)
- repycudd (https://github.com/pysmt/repycudd)
- pyPicoSAT (https://github.com/pysmt/pyPicoSAT)

For instruction on how to use any SMT-LIB complaint solver with pySMT
see `examples/generic_smtlib.py </examples/generic_smtlib.py>`_

For more information, refer to online `documentation on ReadTheDocs <http://pysmt.readthedocs.io>`_

Solvers Support
---------------

The following table summarizes the features supported via pySMT for
each of the available solvers.

 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | Solver           | pySMT name|  Supported Theories            | Quantifiers | Quantifier Elimination | Unsat Core | Interpolation|
 +==================+===========+================================+=============+========================+============+==============+
 | MathSAT          |  msat     | UF, LIA, LRA, BV, AX           |  No         | msat-fm, msat-lw       | Yes        | Yes          |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | Z3               |  z3       | UF, LIA, LRA, BV, AX, NRA, NIA |  Yes        | z3                     | Yes        | No           |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | CVC4             |  cvc4     | UF, LIA, LRA, BV, AX, S        |  Yes        | No                     | No         | No           |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | Yices            |  yices    | UF, LIA, LRA, BV               |  No         | No                     | No         | No           |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | Boolector        |  btor     | UF, BV, AX                     |  No         | No                     | No         | No           |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | SMT-Lib Interface|  <custom> | UF, LIA, LRA, BV, AX           |  Yes        | No                     | No         | No           |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | PicoSAT          |  picosat  | [None]                         |  No         | [No]                   | No         | No           |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+
 | BDD (CUDD)       |  bdd      | [None]                         |  Yes        | bdd                    | No         | No           |
 +------------------+-----------+--------------------------------+-------------+------------------------+------------+--------------+




License
=======

pySMT is released under the APACHE 2.0 License.

For further questions, feel free to open an issue, or write to
pysmt@googlegroups.com (`Browse the Archive <https://groups.google.com/d/forum/pysmt>`_).

If you use pySMT in your work, please consider citing:

.. code::

  @inproceedings{pysmt2015,
    title={PySMT: a solver-agnostic library for fast prototyping of SMT-based algorithms},
    author={Gario, Marco and Micheli, Andrea},
    booktitle={SMT Workshop 2015},
    year={2015}
  }
