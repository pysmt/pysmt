.. _getting-started:

Getting Started
===============

In this section we will see how to install pySMT and how to solve a
simple problem using it.

.. _gs-installation:

Installation
------------

To run pySMT you need Python 3.5+ installed.
If no solver is installed, pySMT can still create and dump the SMT
problem in SMT-LIB format. pySMT works with any SMT-LIB compatible
solver. Moreover, pySMT can leverage the API of the following solvers:

* MathSAT (http://mathsat.fbk.eu/)
* Z3 (https://github.com/Z3Prover/z3/)
* CVC4 (http://cvc4.cs.nyu.edu/web/)
* Yices 2 (http://yices.csl.sri.com/)
* CUDD (http://vlsi.colorado.edu/~fabio/CUDD/)
* PicoSAT (http://fmv.jku.at/picosat/)
* Boolector (http://fmv.jku.at/boolector/)

The Python binding for the SMT Solvers must be installed and
accessible from your ``PYTHONPATH``.

To check which solvers are visible to pySMT, you can use the command
``pysmt-install`` (simply ``install.py`` in the sources)::

  $ pysmt-install --check

provides the list of installed solvers (and version). Solvers can be
installed with the same script: e.g., ::

  $ pysmt-install --msat

installs the MathSAT5 solver.

By default the solvers are downloaded, unpacked and built in your home directory
in the ``.smt_solvers`` folder. Compiled libraries and actual solver packages are
installed in the relevant ``site-packages`` directory (e.g. virtual environment's
packages root or local user-site).

If you specified a custom ``--bindings-path`` during install, you
can use the ``--env`` option to obtain a string to update your
``PYTHONPATH``. When defaults are used, there's not need to update
the ``PYTHONPATH``. ``pysmt-install`` has many options to
customize its behavior.

.. _gs-hello-world:

GMPY2
"""""

PySMT supports the use of the
`gmpy2 <https://gmpy2.readthedocs.io/en/latest/>`_ library (version
2.0.8 or later)
to handle multi-precision numbers. This provides an efficient way to
perform operations on big numbers, especially when fractions are
involved. The gmpy library is used by default if it is installed,
otherwise the ``fractions`` module from Python's standard library is
used. The use of the gmpy library can be controlled by setting the
system environment variables ``PYSMT_GMPY2`` to ``True`` or
``False``. If this is set to true and the gmpy library cannot be
imported, an exception will be thrown.

Cython
""""""

PySMT supports the use of `Cython <http://cython.org/>`_ in order to
improve the performances of some internal component. If Cython is
installed, this will be used (by default) to compile the SMT-LIB
parser. The use of Cython can be controlled by setting the environment
variable ``PYSMT_CYTHON`` to ``True`` or ``False``. If set to false,
the default pure python implementation will be used.


Hello World
-----------

Any decent tutorial starts with a *Hello World* example. We will
encode a problem as an SMT problem, and then invoke a solver to solve
it. After digesting this example, you will be able to perform the most
common operations using pySMT.


The Problem
"""""""""""

The problem that we are going to solve is the following:

  Lets consider the letters composing the words *HELLO* and *WORLD*,
  with a possible integer value between 1 and 10 to each of them.

  Is there a value for each letter so that H+E+L+L+O = W+O+R+L+D = 25?

The Basics
""""""""""

The module :py:mod:`pysmt.shortcuts` provides the most used functions of the
library. These are simple wrappers around functionalities provided by
other objects, therefore, this represents a good starting point if you
are interested in learning more about pySMT.

We include the methods to create a new
:py:meth:`~pysmt.shortcuts.Symbol` (i.e., variables), and
typing information (the domain of the variable), that is defined in
:py:mod:`pysmt.typing`, and we can write the following:

.. literalinclude:: code_snippets/hello_world_infix.py

When importing :py:mod:`pysmt.shortcuts`, the infix notation is
enabled by default. Infix notation makes it very easy to experiment
with pySMT expressions (e.g., on the shell), however, it tends to make
complex code less clear, since it blurs the line between Python
operators and SMT operators. In the rest of the example, we will use
the textual operators by importing them from
:py:mod:`pysmt.shortcuts`.

.. literalinclude:: code_snippets/hello_world_opening.py

Instead of defining one variable at the time, we will use Python's
comprehension to apply the same operation to multiple
symbols. Comprehensions are so common in pySMT that n-ary operators
(such as
:py:meth:`~pysmt.shortcuts.And`,
:py:meth:`~pysmt.shortcuts.Or`,
:py:meth:`~pysmt.shortcuts.Plus`) can accept am iterable object
(e.g. lists or generator).


.. literalinclude:: code_snippets/hello_world.py
                    :lines: 1-22

.. note:: Limited serialization

          By default printing of a string is limited in depth. For big
          formulas, you will see something like ``(x & (y | ... ))``,
          where deep levels of nestings are replaced with the ellipses
          ``...``. This generally provides you with an idea of how the
          structure of the formula looks like, without flooding the
          output when formulas are huge. If you want to print the
          whole formula, you need to call the
          :py:meth:`~pysmt.fnode.FNode..serialize()` method: ::

              print(formula) # (x & (y | ... ))
              print(formula.serialize()) # (x & (y | (z | y)))



Defaults methods for formula allow for simple printing. Checking
satisfiability can also be done with a one-liner.

.. literalinclude:: code_snippets/hello_world_is_sat.py
		 :lines: 25-

Model extraction is provided by the :py:meth:`~pysmt.shortcuts.get_model` shortcut: if the
formula is unsatisfiable, it will return ``None``, otherwise a
:py:class:`~pysmt.solvers.solver.Model`, that is a dict-like structure
mapping each Symbol to its value.

.. literalinclude:: code_snippets/hello_world_is_sat.py
		 :lines: 23-

Shortcuts are very useful for one off operations. In many cases,
however, you want to create an instance of a
:py:class:`~pysmt.solvers.solver.Solver` and operate on it
incrementally. This can be done using the
:py:meth:`pysmt.shortcuts.Solver` factory. This factory can be used
within a context (``with`` statement) to automatically handle
destruction of the solver and associated resources. After creating the
solver, we can assert parts of the formula and check their
satisfiability. In the following snippet, we first check that the
``domain`` formula is satisfiable, and if so, we continue to solve the
problem.

.. literalinclude:: code_snippets/hello_world.py
		  :lines: 22-

In the example, we access the value of each symbol
(:py:meth:`~pysmt.solvers.solver.Solver.get_value`), however, we can
also obtain a model object using :py:meth:`~pysmt.solvers.solver.Solver.get_model`.

.. note:: Incrementality and Model Construction

   Many solvers can perform aggressive simplifications if
   incrementality or model construction are not required. Therefore,
   if you do not need incrementality and model construction, it is
   better to call :py:meth:`~pysmt.shortcuts.is_sat`, rather than instantiating a
   solver. Similarly, if you need only one model, you should use
   :py:meth:`~pysmt.shortcuts.get_model`


With pySMT it is possible to run the same code by using different
solvers. In our example, we can specify which solver we want to run by
changing the way we instantiate it. If any other solver is installed,
you can try it by simply changing ``name="z3"`` to its codename (e.g., ``msat``):

=========   ==========
Solver      pySMT name
=========   ==========
MathSAT     msat
Z3          z3
CVC4        cvc4
Yices       yices
Boolector   btor
Picosat     picosat
CUDD        bdd
=========   ==========

You can also not specify the solver, and simply state which Logic must
be supported by the solver, this will look into the installed solvers
and pick one that supports the logic. This might raise an exception
(:py:class:`~pysmt.exceptions.NoSolverAvailableError`), if no logic for
the logic is available.

Here is the complete example for reference using the logic QF_LIA:

.. literalinclude:: code_snippets/hello_world_qf_lia.py


What's Next?
------------

This simple example provides the basic ideas of how to work with
pySMT. The best place to understand more about pySMT is the
:py:mod:`pysmt.shortcuts` module. All the important functionalities are exported
there with a simple to use interface.

To understand more about other functionalities of pySMT, you can take
a look at the `examples/ folder <https://github.com/pysmt/pysmt/blob/master/examples/README.rst>`_ .
