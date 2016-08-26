.. _api-ref:

=============
API Reference
=============

.. contents::
   :local:

Shortcuts
=========
.. automodule:: pysmt.shortcuts

Solver, Model, QuantifierEliminator, Interpolator, and UnsatCoreSolver
======================================================================
.. autoclass:: pysmt.solvers.solver.Solver
.. autoclass:: pysmt.solvers.solver.Model
.. autoclass:: pysmt.solvers.qelim.QuantifierEliminator
.. autoclass:: pysmt.solvers.interpolation.Interpolator
.. autoclass:: pysmt.solvers.solver.UnsatCoreSolver

Environment
===========
.. automodule:: pysmt.environment


Exceptions
==========
.. automodule:: pysmt.exceptions

Factory
=======
.. automodule:: pysmt.factory

FNode
=====
.. automodule:: pysmt.fnode

Formula
=======
.. automodule:: pysmt.formula

Logics
======
.. automodule:: pysmt.logics

Operators
=========
.. automodule:: pysmt.operators

Oracles
=======
.. automodule:: pysmt.oracles

Parsing
=======
.. autofunction:: pysmt.parsing.parse
.. autofunction:: pysmt.parsing.HRParser

Printers
========
.. automodule:: pysmt.printers

Simplifier
==========
.. automodule:: pysmt.simplifier

SMT-LIB
==========

.. automodule:: pysmt.smtlib.parser
.. automodule:: pysmt.smtlib.printers
.. automodule:: pysmt.smtlib.script
.. automodule:: pysmt.smtlib.solver
.. automodule:: pysmt.smtlib.commands
.. automodule:: pysmt.smtlib.annotations


Substituter
===========
.. automodule:: pysmt.substituter

Type-Checker
============
.. automodule:: pysmt.type_checker

Typing
======
.. automodule:: pysmt.typing


Walkers
=======
.. automodule:: pysmt.walkers
.. autoclass:: pysmt.walkers.DagWalker
.. autoclass:: pysmt.walkers.TreeWalker
.. autoclass:: pysmt.walkers.IdentityDagWalker
