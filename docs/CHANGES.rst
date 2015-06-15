Change Log
==========

0.4.0: 2015-06-15 -- Interpolation and BDDs
--------------------------------------------

General:

* Craig interpolation support through Interpolator class,
  binary_interpolant and sequence_interpolant shortcuts.
  Current support is limited to MathSAT and Z3.
  Thanks to Alberto Griggio for implementing this!

* Rewriting functions: nnf-ization, prenex-normalization and
  disjunctive/conjunctive partitioning.

* get_implicant(): Returns the implicant of a satisfiable formula.

* Improved support for infix notation.

* Z3Model Iteration bugfix

BDDs:

* Switched from pycudd wrapper to a custom re-entrant version
  called repycudd (https://github.com/pysmt/repycudd)

* Added BDD-Based quantifier eliminator for BOOL theory

* Added support for static/dynamic variable ordering

* Re-implemented back-conversion avoiding recursion


0.3.0: 2015-05-01  -- BitVectors/UnsatCores
-------------------------------------------

Theories:

* Added initial support for BitVectors and QF_BV logic.
  Current support is limited to MathSAT and unsigned operators.

Solvers:

* Two new quantifier eliminators for LRA using MathSAT API:
  Fourier-Motzkin (msat_fm) and Loos-Weisspfenning (msat_lw)

* Yices: Improved handling of int/real precision

General:

* Unsat Cores: Unsat core extraction with dedicated shortcut
  get_unsat_core . Current support is limited to MathSAT and Z3

* Added support for Python 3. The library now works with both Python 2
  and Python 3.

* QuantifierEliminator and qelim shortcuts, as well as the respective
  factory methods can now accept a 'logic' parameter that allows to
  select a quantifier eliminator instance supporting a given logic
  (analogously to what happens for solvers).

* Partial Model Support: Return a partial model whenever possible.
  Current support is limited to MathSAT and Z3.

* FNode.size(): Added method to compute the size of an expression
  using multiple metrics.


0.2.4: 2015-03-15  -- PicoSAT
-----------------------------

Solvers:

* PicoSAT solver support

General:

* Iterative implementation of FNode.get_free_variables().
  This also deprecates FNode.get_dependencies().

Bugfix:

* Fixed bug (#48) in pypi package, making pysmt-install (and other commands) unavailable. Thanks to Rhishikesh Limaye for reporting this.

0.2.3: 2015-03-12 -- Logics Refactoring
---------------------------------------

General:

* install.py: script to automate the installation of supported
  solvers.

* get_logic() Oracle: Detects the logic used in a formula. This can now be used in the shortcuts (_is_sat()_, _is_unsat()_, _is_valid()_, and
  _get_model()_) by choosing the special logic pysmt.logics.AUTO.

* Expressions: Added Min/Max operators.

* SMT-LIB: Substantially improved parser performances. Added explicit
  Annotations object to deal with SMT-LIB Annotations.

* Improved iteration methods on EagerModel

**Backwards Incompatible Changes**:

* The default logic for Factory.get_solver() is now the most generic
  *quantifier free* logic supported by pySMT (currently,
  QF_UFLIRA). The factory not provides a way to change this default.

* Removed option _quantified_ from all shortcuts.




0.2.2: 2015-02-07 -- BDDs
-------------------------

Solvers:

* pyCUDD to perform BDD-based reasoning

General:

* Dynamic Walker Function: Dynamic Handlers for new node types can now
  be registered through the environment (see
  Environment.add_dynamic_walker_function).

0.2.1: 2014-11-29 -- SMT-LIB
----------------------------

Solvers:

* Yices 2
* Generic Wrapper: enable usage of any SMT-LIB compatible solver.

General:

* SMT-LIB parsing
* Changed internal representation of FNode
* Multiple performance improvements
* Added configuration file


0.2.0: 2014-10-02 -- Beta release.
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


0.1.0: 2014-03-10 -- Alpha release.
-----------------------------------

Theories: LIA, LRA, RDL, EUF
Solvers: MathSAT, Z3
General Functionalities:

* Formula Manipulation: Creation, Simplification, Substitution, Printing
* Uniform Solving for QF formulae
* Unified Quantifier Elimination (Z3 support only)


0.0.1: 2014-02-01 -- Initial release.
-------------------------------------
