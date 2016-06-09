Change Log
==========

0.5.0: 2016-06-09 -- Arrays
---------------------------

BACKWARDS INCOMPATIBLE CHANGES:

* MGSubstituter becomes the new default substitution method (PR #253)

  When performing substitution with a mapping like ```{a: b, Not(a),
  c}```, ```Not(a)``` is considered before ```a```. The previous
  behavior (MSSubstituter) would have substituted ```a``` first, and
  then the rule for ```Not(a)``` would not have been applied.

* Removed argument ```user_options``` from Solver()

Theories:

* Added support for the Theory of Arrays.

  In addition to the SMT-LIB definition, we introduce the concept of
  Constant Array as supported by MathSAT and Z3. The theory is
  currently implemented for MathSAT, Z3, Boolector, CVC4.

  Thanks to **Alberto Griggio**, **Satya Uppalapati** and **Ahmed
  Irfan** for contributing through code and discussion to this
  feature.

General:

* Simplifier: Enable simplification if IFF with constant:
  e.g., (a <-> False) into !a

* Automatically enable Infix Notation by importing shortcuts.py (PR #267)

* SMT-LIB: support for define-sort commands without arguments

* Improved default options for shortcuts:

  * Factory.is_* sets model generation and incrementality to False;
  * Factory.get_model() sets model generation to True, and
    incrementality to False.
  * Factory.Solver() sets model generation and incrementality to True;

* Improved handling of options in Solvers (PR #250):

  Solver() takes **options as free keyword arguments. These options
  are checked by the class SolverOptions, in order to validate that
  these are meaningful options and perform a preliminary validation to
  catch typos etc. by raising a ValueError exception if the option is
  unknown.

  It is now possible to do: ```Solver(name="bdd", dynamic_reordering=True)```


Solvers:

* rePyCUDD: Upgrade to 75fe055 (PR #262)
* CVC4: Upgrade to c15ff4 (PR #251)
* CVC4: Enabled Quantified logic (PR #252)


Bugfixes:

* Fixed bug in Non-linear theories comparison
* Fixed bug in reset behavior of CVC4
* Fixed bug in BTOR handling of bitwidth in shifts
* Fixed bug in BTOR's get_value function
* Fixed bug in BTOR, when operands did not have the same width after rewriting.


0.4.4: 2016-05-07 -- Minor
--------------------------

General:

* BitVectors: Added support for infix notation
* Basic performance optimizations

Solvers:

* Boolector: Upgraded to version 2.2.0

Bugfix:

* Fixed bug in ExactlyOne args unpacking. Thanks to **Martin**
  @hastyboomalert for reporting this.



0.4.3: 2015-12-28 -- Installers and HR Parsing
----------------------------------------------

General:

* pysmt.parsing: Added parser for Human Readable expressions
* pysmt-install: new installer engine
* Most General Substitution: Introduced new Substituter, that performs
top-down substitution. This will become the default in version 0.5.
* Improved compliance with SMT-LIB 2 and 2.5
* EagerModel can now take a solver model in input
* Introduce new exception 'UndefinedSymbolError' when trying to access
  a symbol that is not defined.
* Logic names can now be passed to shortcuts methods (e.g., is_sat) as
  a string


Solvers:

* MathSAT: Upgraded to version 5.3.9, including support for new
  detachable model feature. Thanks to **Alberto Griggio** for
  contributing this code.
* Yices: Upgraded to version 2.4.1
* Shannon: Quantifier Elimination based on shannon expansion (shannon).
* Improved handling of Context ('with' statement), exit and __del__ in
  Solvers.


Testing:

* Introduced decorator pysmt.test.skipIfNoSMTWrapper
* Tests do note explicitely depend anymore on unittest module.  All
  tests that need to be executable only need to import
  pysmt.test.main.


Bugfix:

* #184:  MathSAT: Handle UF with boolean args
  Fixed incorrect handling of UF with bool arguments when using
  MathSAT. The converter now takes care of rewriting the formula.
* #188: Auto-conversion of 0-ary functions to symbols
* #204: Improved quoting in SMT-LIB output
* Yices: Fixed a bug in push() method
* Fixed bug in Logic name dumping for SMT-LIB
* Fixed bug in Simplifier.walk_plus
* Fixed bug in CNF Converter (Thanks to Sergio Mover for pointing this out)


Examples:

* parallel.py: Shows how to use multi-processing to perform parallel and asynchronous solving
* smtlib.py: Demonstrates how to perform SMT-LIB parsing, dumping and extension
* einstein.py: Einstein Puzzle with example of debugging using UNSAT-Cores.



0.4.2: 2015-10-12 -- Boolector
-----------------------------------------

Solvers:

* Boolector 2.1.1 is now supported
* MathSAT: Updated to 5.3.8


General:

* EqualsOrIff: Introduced shortcut to handle equality and mismatch
  between theory and predicates atoms. This simply chooses what to use
  depending on the operands: Equals if Theory, Iff if predicates.
  Example usage in examples/all_smt.py

* Environment Extensibility: The global classes defined in the
  Environment can now be replaced. This makes it much easier for
  external tools to define new FNode types, and override default
  services.

* Parser Extensibility: Simplified extensibility of the parser by
  splitting the special-purpose code in the main loop in separate
  functions. This also adds support for escaping symbols when dealing
  with SMT-LIB.

* AUTO Logic: Factory methods default to logics.AUTO, providing a
  smarter selection of the logic depending on the formula being
  solved. This impacts all is_* functions, get_model, and qelim.

* Shell: Import BV32 and BVType by default, and enable infix notation

* Simplified HRPrinter

* Added AIG rewriting (rewritings.AIGer)

Bugfix:

* Fixed behavior of CNFizer.cnf_as_set()
* Fixed issue #159: error in parsing let bindings that refer to
  previous let-bound symbols.
  Thanks to *Alberto Griggio* for reporting it!


0.4.1: 2015-07-13 -- BitVectors Extension
-----------------------------------------

Theories:

* BitVectors: Added Signed operators

Solvers:

* Support for BitVectors added for Z3, CVC4, and Yices

General:

* SmartPrinting: Print expression by replacing sub-expression with
  custom strings.

* Moved global environment initialization to environment.py. Now
  internal functions do no need to import shortcuts.py anymore, thus
  breaking some circular dependencies.

Deprecation:

* Started deprecation of get_dependencies and get_sons
* Depreaced Randomizer and associated functions.


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
