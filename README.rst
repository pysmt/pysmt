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

Supported Theories and Solvers
==============================
pySMT provides methods to define a formula in Linear Real Arithmetic (LRA), Real Difference Logic (RDL), their combination (LIRA),
Equalities and Uninterpreted Functions (EUF) and Bit-Vectors (BV). The following solvers are supported through native APIs:

* MathSAT (http://mathsat.fbk.eu/) >= 5
* Z3 (http://z3.codeplex.com/releases) >= 4
* CVC4 (http://cvc4.cs.nyu.edu/web/)
* Yices 2 (http://yices.csl.sri.com/)
* repycudd (https://github.com/pysmt/repycudd)
* PicoSAT (http://fmv.jku.at/picosat/)

Additionally, you can use any SMT-LIB 2 compliant solver.

PySMT assumes that the python bindings for the SMT Solver are installed and accessible from your PYTHONPATH. For Yices 2 we rely on pyices (https://github.com/cheshire/pyices).

pySMT works on both Python 2 and Python 3. Some solvers support both versions (e.g., MathSAT) but in general, many solvers still support only Python 2.


The following table summarizes the features supported via pySMT for
each of the available solvers. (We indicate with square brackets the
features that are supported by the solver itself by not by the current
wrapper used within pySMT).

  =================   ==========   ==================   ==============   ==================   ==========
  Solver              pySMT name   Supported Logics     Satisfiability   Model Construction   UNSAT-Core
  =================   ==========   ==================   ==============   ==================   ==========
  MathSAT             msat         QF_UFLIRA, QF_BV     Yes              Yes                  Yes
  Z3                  z3           UFLIRA, [QF_BV]      Yes              Yes                  Yes
  CVC4                cvc4         QF_UFLIRA, [QF_BV]   Yes              Yes                  No
  Yices               yices        QF_UFLIRA, [QF_BV]   Yes              Yes                  No
  SMT-Lib Interface   <custom>     UFLIRA, [QF_BV]      Yes              Yes                  No [Yes]
  PicoSAT             picosat      QF_BOOL              Yes              Yes                  No [Yes]
  BDD (CUDD)          bdd          BOOL                 Yes              Yes                  No
  =================   ==========   ==================   ==============   ==================   ==========

The following table summarizes the features supported via pySMT for each of the available quantifier eliminators

  =====================   ==========   ================
  Quantifier Eliminator   pySMT name   Supported Logics
  =====================   ==========   ================
  MathSAT FM              msat-fm      LRA
  MathSAT LW              msat-lw      LRA
  Z3                      z3           LRA, LIA
  BDD (CUDD)              bdd          BOOL
  =====================   ==========   ================

The following table summarizes the features supported via pySMT for each of the available Craig interpolators

  ============   ==========   =========================
  Interpolator   pySMT name   Supported Logics
  ============   ==========   =========================
  MathSAT        msat         QF_UFLIA, QF_UFLRA, QF_BV
  Z3             z3           QF_UFLIA, QF_UFLRA
  ============   ==========   =========================


Getting Started
===============
You can install the latest stable release of pySMT from PyPI:

  # pip install pysmt
this will additionally install the *pysmt-install* command, that can be used to install the solvers: e.g.,

  $ pysmt-install --check
will show you which solvers have been found in your PYTHONPATH. For instructions on how to install each solver refer to the section on *solvers installation*.

Usage
=====

.. code:: python

  from pysmt.shortcuts import Symbol, And, Not, is_sat

  varA = Symbol("A") # Default type is Boolean
  varB = Symbol("B")
  f = And([varA, Not(varB)])
  g = f.substitute({varB:varA})

  res = is_sat(f)
  assert res # SAT
  print("f := %s is SAT? %s" % (f, res))

  res = is_sat(g)
  print("g := %s is SAT? %s" % (g, res))
  assert not res # UNSAT


A more complex example is the following:

Lets consider the letters composing the words *HELLO* and *WORLD*,
with a possible integer value between 1 and 10 to each of them.
Is there a value for each letter so that H+E+L+L+O = W+O+R+L+D = 25?

The following is the pySMT code for solving this problem:

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


Solvers Installation
====================

PySMT does not depend directly on any solver. If you want to perform solving, you need to have at least one solver installed, and then call it via pySMT either through its native API, or passing through an SMT-LIB file.

The script *pysmt-install* can be used to simplify the installation of the solvers:

 $ pysmt-install --msat
will install MathSAT 5. This script does not install required dependencies for building the solver (e.g., make or gcc) and has been tested mainly on Linux Debian/Ubuntu systems. We suggest that you refer to the documentation of each solver to understand how to install it with its python bindings. Nevertheless, we try to keep *pysmt/cmd/install.py* as readable and documented as possible..

Finally, for CVC4 and picosat, we have patches that need to be applied. The patches are available in the repository 'pysmt/solvers_patches' and should be applied against the following versions of the solvers:

- CVC4: Git revision 68f22235a62f5276b206e9a6692a85001beb8d42
- pycudd: 2.0.2
- picosat 960

For instruction on how to use any SMT-LIB complaint solver with pySMT see examples/generic_smtlib.py
