Change Log
==========

0.2.3 XXXXXXXXXX -- YYY
-----------------------

General:

* install.py: script to automate the installation of supported
  solvers.

* Expressions: Added Min/Max operators.

0.2.2 2015-02-07 -- BDDs
------------------------

Solvers:

* pyCUDD to perform BDD-based reasoning

General:

* Dynamic Walker Function: Dynamic Handlers for new node types can now
  be registered through the environment (see
  Environment.add_dynamic_walker_function).

0.2.1 2014-11-29 -- SMT-LIB
---------------------------

Solvers:

* Yices 2
* Generic Wrapper: enable usage of any SMT-LIB compatible solver.

General:

* SMT-LIB parsing
* Changed internal representation of FNode
* Multiple performance improvements
* Added configuration file


0.2.0 2014-10-02 -- Beta release.
----------------------------------

Theories: LIRA
Solvers: CVC4
General:

* Type-checking
* Definition of SMT-LIB logics
* Converted the DAGWalker from recursive to iterative
* Better handling of errors during formula creation and solving
* Preferences among available solvers.

Deprecation:

* Option 'quantified' within Solver() and all related methods will be
  removed in the next release.

Backwards Incompatible Changes:

* Renamed the module pysmt.types into pysmt.typing, to avoid conflicts
  with the Python Standard Library.


0.1.0 2014-03-10 -- Alpha release.
----------------------------------

Theories: LIA, LRA, RDL, EUF
Solvers: MathSAT, Z3
General Functionalities:

* Formula Manipulation: Creation, Simplification, Substitution, Printing
* Uniform Solving for QF formulae
* Unified Quantifier Elimination (Z3 support only)


0.0.1 2014-02-01 -- Initial release.
------------------------------------
