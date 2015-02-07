============================================================
 pySMT: A library for SMT formulae manipulation and solving
============================================================

pySMT makes working with Satisfiability Modulo Theory simple.

Among others, you can:

* Define formulae in a solver independent way in a simple and
  inutitive way,
* Write ad-hoc simplifiers and operators,
* Dump your problems in the SMT-Lib format,
* Solve them using one of the native solvers, or by wrapping any
  SMT-Lib complaint solver.


.. image:: https://api.shippable.com/projects/54d4edba5ab6cc13528b1970/badge?branchName=master
           :target: https://app.shippable.com/projects/54d4edba5ab6cc13528b1970/builds/latest
           :alt: Build Status

.. image:: https://readthedocs.org/projects/pysmt/badge/?version=latest
           :target: https://readthedocs.org/projects/pysmt/?badge=latest
           :alt: Documentation Status


Requirements
============

* Python (http://www.python.org) >= 2.6
* MathSAT (http://mathsat.fbk.eu/) >= 5 (Optional)
* Z3 (http://z3.codeplex.com/releases) >= 4 (Optional)
* CVC4 (http://cvc4.cs.nyu.edu/web/) (Optional)
* Yices 2 (http://yices.csl.sri.com/) (Optional)
* pyCUDD (http://bears.ece.ucsb.edu/pycudd.html) (Optional)

The library assumes that the python binding for the SMT Solver are installed
and accessible from your PYTHONPATH.
For Yices 2 we rely on pyices (https://github.com/cheshire/pyices).


Supported Theories
==================

pySMT provides methods to define a formula in Linear Real Arithmetic
(LRA), Real Difference Logic (RDL), their combination (LIRA) and
Equalities and Uninterpreted Functions (EUF).


Usage
=====

.. code:: python

  from pysmt.shortcuts import Symbol, And, Not, FALSE, Solver

  with Solver() as solver:

      varA = Symbol("A") # Default type is Boolean
      varB = Symbol("B")

      f = And([varA, Not(varB)])

      print(f)

      g = f.substitute({varB:varA})

      print(g)

      solver.add_assertion(g)
      res = solver.solve()
      assert not res

      h = And(g, FALSE())
      simp_h = h.simplify()
      print(h, "-->", simp_h)


A more complex example is the following:

Lets consider the letters composing the words *HELLO* and *WORLD*,
with a possible integer value between 1 and 10 to each of them.
Is there a value for each letter so that H+E+L+L+O = W+O+R+L+D = 25?

The following is the pySMT code for solving this problem:

.. code:: python

  from pysmt.shortcuts import Symbol, LE, GE, Int, And, Equals, Plus, Solver
  from pysmt.typing import INT

  hello = [Symbol(s, INT) for s in "hello"]
  world = [Symbol(s, INT) for s in "world"]

  letters = set(hello+world)

  domains = And([And(LE(Int(1), l),
                     GE(Int(10), l) ) for l in letters])

  sum_hello = Plus(hello) # n-ary operators can take lists
  sum_world = Plus(world) # as arguments

  problem = And(Equals(sum_hello, sum_world),
                Equals(sum_hello, Int(25)))

  formula = And(domains, problem)

  print("Serialization of the formula:")
  print(formula)

  # Use context to create and free a solver. Solver are selected by name
  # and can be used in a uniform way (try name="msat")
  with Solver(name="z3") as solver:
      solver.add_assertion(formula)
      if solver.solve():
         for l in letters:
            print("%s = %s" %(l, solver.get_value(l)))
      else:
        print("No solution found")
