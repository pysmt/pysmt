Getting Started
===============

In this section we will see how to install pySMT and how to solve a
simple problem using it.

Installation
------------

To run pySMT you need python 2.7 or python 3.5+ installed.
If no solver is installed, pySMT can still create and dump the SMT
problem in SMT-LIB format. pySMT works with the following solvers:

* MathSAT (http://mathsat.fbk.eu/)
* Z3 (https://github.com/Z3Prover/z3/)
* CVC4 (http://cvc4.cs.nyu.edu/web/)
* Yices 2 (http://yices.csl.sri.com/)
* CUDD (http://vlsi.colorado.edu/~fabio/CUDD/)
* PicoSAT (http://fmv.jku.at/picosat/)
* Boolector (http://fmv.jku.at/boolector/)

The python binding for the SMT Solvers must be installed and
accessible from your PYTHONPATH.


Hello World
-----------

Any decent tutorial starts with an *Hello World* example. We will
encode a problem as an SMT problem, and then invoke a solver to solve
it. After digesting this example, you will be able to perform the most
common operations using pySMT.


The Problem
~~~~~~~~~~~

The problem that we are going to solve is the following:

  Lets consider the letters composing the words *HELLO* and *WORLD*,
  with a possible integer value between 1 and 10 to each of them.

  Is there a value for each letter so that H+E+L+L+O = W+O+R+L+D = 25?

The Basics
~~~~~~~~~~

The module :py:mod:`pysmt.shortcuts` provides the most used functions of the
library. These are simple wrappers around functionalities provided by
other objects, therefore, this represents a good starting point if you
are interested in learning more about pySMT internals.

We first include the methods needed to define new symbols (i.e.,
varibles) and operators. The types available for constants are defined
in :py:mod:`pysmt.typing`.

.. literalinclude:: code_snippets/hello_world_opening.py

Instead of defining one variable at the time, we will use python list
comprehension to apply the same operation to multiple
symbols. List-comprehensions are so common in pySMT that n-ary
operators (such as ``And``, ``Or``, ``Plus``) can accept lists of
arguments.

.. literalinclude:: code_snippets/hello_world.py

Defaults methods for formula allow for simple printing. Checking
satisfiability can also be done with a one-liner.

.. literalinclude:: code_snippets/hello_world_is_sat.py
		 :lines: 22-

Althoug checking satisfiability is quite straight-forward, extract a
models requires working with an explicit instance of a solver.
Solvers can be instantiate within a context (``with``) to
automatically handle destruction. After creating the solver, we can
assert the forumla and query the solver.

.. literalinclude:: code_snippets/hello_world.py
		  :lines: 22-

The key-point of pySMT is to be able to run the same code by using
different solvers. In our example, we can specify which solver we want
to run by changing the way we instantiate it. If mathsat is installed
you can try by replacing ``name="z3"`` with ``name="msat"``.

Here is the complete example for reference:

.. literalinclude:: code_snippets/hello_world.py

What's Next?
------------

This simlpe example provides the basic ideas of how to work with
pySMT. The best place to understand more about pySMT is the
:py:mod:`pysmt.shortcuts` module. All the important functionalities are exported
there with a simple to use interface.
