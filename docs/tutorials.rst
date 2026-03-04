Tutorials
=========

This page is under-construction. For now, it contains a copy of the
files within the `examples/ folder
<https://github.com/pysmt/pysmt/blob/master/examples/README.rst>`_ of
the pySMT repository and a basic tutorial on Boolean logic.

If you are interested in helping us create better tutorials, please
let us know at info@pysmt.org .


.. contents::
   :local:


Boolean Logic in PySMT
----------------------
An introductory basic example on how to use pySMT for Booean satisfiability: :ref:`pysmt-tutorials-booleanlogic`.

First example
-------------
.. literalinclude:: ../examples/basic.py

Hello World word puzzle
-----------------------
.. literalinclude:: ../examples/puzzle.py

Hello World word puzzle using infix-notation
--------------------------------------------
.. literalinclude:: ../examples/infix_notation.py

Combine multiple solvers
------------------------------------------
.. literalinclude:: ../examples/combine_solvers.py

Model-Checking an infinite state system (BMC+K-Induction) in ~150 lines
-----------------------------------------------------------------------
.. literalinclude:: ../examples/model_checking.py

How to access functionalities of solvers not currently wrapped by pySMT
-----------------------------------------------------------------------
.. literalinclude:: ../examples/allsat.py

How to use any SMT-LIB compliant SMT solver
--------------------------------------------
.. literalinclude:: ../examples/generic_smtlib.py

How to combine two different solvers to solve an Exists Forall problem
----------------------------------------------------------------------
.. literalinclude:: ../examples/efsmt.py

How to detect the logic of a formula and perform model enumeration
------------------------------------------------------------------
.. literalinclude:: ../examples/allsmt.py

Shows how to use multi-processing to perform parallel and asynchronous solving
------------------------------------------------------------------------------
.. literalinclude:: ../examples/parallel.py

Demonstrates how to perform SMT-LIB parsing, dumping and extension
------------------------------------------------------------------
.. literalinclude:: ../examples/smtlib.py

Shows the use of UNSAT Core as debugging tools
----------------------------------------------
.. literalinclude:: ../examples/einstein.py
