Change Log
==========

0.7.0: 2017-08-12 -- Class Based Walkers and Sorts
--------------------------------------------------

BACKWARDS INCOMPATIBLE CHANGES:

* Removed option "quantified" in Solver (PR #377)

* Removed deprecated CNFizer.printer method (PR #359)

General:

* Class-Based Walkers (PR #359):

  Walkers behavior is now defined in the class definition.  Processing
  an AND node always calls walk_and. This makes it possible to
  subclass and override methods, but at the same time call the
  implementation of a super class, e.g.::

     def walk_and(...):
          return ParentWalker.walk_and(self, ....)

  The utility method Walker.super is provided to automatically handle the
  dispatch of a node to the correct walk_* function, e.g.,::

    def walk_bool_to_bool(...):
        return ParentWalker._super(self, ....)

  The method Walker.set_functions is deprecated, but kept for
  compatibility with old-style walkers. Using set_functions has the same
  effect as before. However, you cannot modify a subclass of a walker
  using set_functions. *You should not be using set_functions anymore!*

  The method Walker.set_handler is used to perform the same operation of
  set_function at the class level. The associated decorator @handles can
  be used to associate methods with nodetypes.

  These changes make it possible to extend the walkers from outside
  pySMT, without relying on hacks like the Dynamic Walker Factory
  (DWF). See examples/ltl.py for a detailed example.

* Introduce the support for custom sorts (PySMTTypes) (PR #375)

  Two new classes are introduced: _Type and PartialType

  PartialType is used to represent the concept of SMT-LIB "define-sort".
  The class _TypeDecl is used to represents a Type declaration, and
  as such cannot be used directly to instantiate a
  Symbol. This capture the semantics of declare-sort. A wrapper
  Type() is given to simplify its use, and making 0-arity sorts a
  special case. The following two statements are equivalent::

    Type("Colors")
    Type("Colors", 0)

  0-ary type are instantiated by default. For n-ary types, the type
  needs to be instantiated. This can be done with the method
  ``TypeManager.get_type_instance`` or by using infix notation (if
  enabled)::

    type_manager.get_type_instance(Type(Pair, 2), Int, Int))
    Type(Pair, 2)(Int, Int)

  Type declarations and Type instances are memoized in the
  environment, and suitable shortucts have been introduced.
  Logics definition has been extended with the field ``custom_types``
  to detect the use of custom types. *Note*: Due to the limited
  support of custom types by solvers, by default every SMT-LIB logic
  is defined with ``custom_types=False``.

* Add shortcuts.to_smtlib() to easily dump an SMT-LIB formula

* Add explicit support for BV and UFBV logics (PR #423): Thanks to
  **Alexey Ignatiev** for reporting this.


Solvers:

* PicoSAT: Upgrade to 965 (PR #425)

* Boolector: Upgrade to 2.4.1 (PR #422)

* CVC4: Fixed memory-leak (PR #419)

* Yices: Upgrade to 2.5.2 (PR #426)


Bugfix:

* Fixed assumption handling in the Boolector wrapper. Thanks to
  **Alexey Ignatiev** for contributing with this patch!

* Fix cyclic imports (PR #406). Thanks to **@rene-rex** for reporting
  this.

* Fixed SMT-LIB Script serialization to default to a daggified
  representation. (PR #418)

* Fixed SMT-LIB Parsing of declare-const . Thanks to
  **@ahmedirfan1983** for reporting this. (PR #429)

* Fixed logic detection when calling is_unsat (PR #428)



0.6.1: 2016-12-02 -- Portfolio and Coverage
-------------------------------------------

General:

* Portfolio Solver (PR #284):

  Created Portfolio class that uses multiprocessing to solve the
  problem using multiple solvers. get_value and get_model work after a
  SAT query. Other artifacts (unsat-core, interpolants) are not
  supported.
  Factory.is_* methods have been extended to include `portfolio`
  key-word, and exported as is_* shortcuts. The syntax becomes::

    is_sat(f, portfolio=["s1", "s2"])

* Coverage has been significantly improved, thus giving raise to some
  clean-up of the tests and minor bug fixes. Thanks to Coveralls.io
  for providing free coverage analysis. (PR #353, PR #358, PR #372)

* Introduce PysmtException, from which all exceptions must
  inherit. This also introduces hybrid exceptions that inherit both
  from the Standard Library and from PysmtException (i.e.,
  PysmtValueError). Thanks to **Alberto Griggio** for
  suggesting this change. (PR #365)

* Windows: Add support for installing Z3. Thanks to **Samuele
  Gallerani** for contributing this patch. (PR #385)

* Arrays: Improved efficiency of array_value_get (PR #357)

* Documentation: Thanks to the **Hacktoberfest** for sponsoring these
  activities:

  * Every function in shortcuts.py now has a docstring! Thanks to
    **Vijay Raghavan** for contributing this patch. (PR #363)

  * Contributing information has been moved to the official
    documentation and prettyfied! Thanks to **Jason Taylor Hodge** for
    contributing this patch. (PR #339)

  * Add link to Google Group in Readme.md . Thanks to @ankit01ojha for
    contributing this. (PR #345)

* smtlibscript_from_formula(): Allow the user to specify a custom
  logic. Thanks to **Alberto Griggio** for contributing this
  patch. (PR #360)

Solvers:

* MathSAT: Improve back-conversion performance by using MSAT_TAGS (PR #379)

* MathSAT: Add LIA support for Quantifier Elimination

* Removed: Solver.declare_variable and Solver.set_options (PR #369, PR #378)

Bugfix:

* CVC4:

  * Enforce BV Division by 0 to return a known value (0xFF) (PR #351)

  * Force absolute import of CVC4. Thanks to **Alexey Ignatiev**
    (@2sev) for reporting this issue. (PR #382)

* MathSAT: Thanks to **Alberto Griggio** for contributing these patches

  * Fix assertions about arity of BV sign/zero extend ops. (PR #350, PR #351)

  * Report the error message generated by MathSAT when raising a
    SolverReturnedUnknownResultError (PR #355)

* Enforce a single call to is_sat in non-incremental mode (PR
  #368). Thanks to @colinmorris for pointing out this issue.

* Clarified Installation section and added example of call to
  ```pysmt-install --env```.  Thanks to **Marco Roveri**
  (@marcoroveri) for pointing this out.

* SMT-LIB Parser:

  * Minor fixes highlighted by fuzzer (PR #376)

  * Fixed annotations parsing according to SMTLib rules (PR #374)

* pysmt-install: Gracefully fail if GIT is not installed (PR #390)
  Thanks to **Alberto Griggio** for reporting this.

* Removed dependency from internet connections when checking picosat
  version (PR #386)


0.6.0: 2016-10-09 -- GMPY2 and Goodbye Recursion
------------------------------------------------

BACKWARDS INCOMPATIBLE CHANGES:

* Integer, Fraction and Numerals are now defined in pysmt.constants
  (see below for details). The breaking changes are:

  * Users should use pysmt.constants.Fraction, if they want to
    guarantee that the same type is being used (different types are
    automatically converted);
  * Methods from pysmt.utils moved to pysmt.constants;
  * Numerals class was moved from pysmt.numeral (that does not exist
    anymore).


* Non-Recursive TreeWalker (PR #322)

  Modified TreeWalker to be non-recursive. The algorithm works by
  keeping an explicit stack of the walking functions **that are now
  required to be generators**. See pysmt.printer.HRPrinter for an
  example. This removes the last piece of recursion in pySMT !


* Times is now an n-ary operator (Issue #297 / PR #304)

  Functions operating on the args of Times (e.g., rewritings) should
  be adjusted accordingly.


* Simplified module pysmt.parsing into a unique file (PR #301)

  The pysmt.parsing module was originally divided in two files:
  pratt.py and parser.py. These files were removed and the parser
  combined into a unique parsing.py file. Code importing those modules
  directly needs to be updated.


* Use solver_options to specify solver-dependent options (PR #338):

  * MathSAT5Solver option 'debugFile' has been removed. Use the
    solver option: "debug_api_call_trace_filename".

  * BddSolver used to have the options as keyword
    arguments (static_ordering, dynamic_reordering etc). This is not
    supported anymore.


* Removed deprecated methods (PR #332):

  * FNode.get_dependencies (use FNode.get_free_variables)
  * FNode.get_sons (use FNode.get_args)
  * FNode.is_boolean_operator (use FNode.is_bool_op)
  * pysmt.test.skipIfNoSolverAvailable
  * pysmt.randomizer (not used and broken)



General:

* Support for GMPY2 to represent Fractions (PR #309).

  Usage of GMPY2 can be controlled by setting the env variable
  PYSMT_GMPY to True or False. By default, pySMT tries to use GMPY2 if
  installed, and fallbacks on Python's Fraction otherwise.


* Constants module: pysmt.constants (PR #309)

  This module provides an abstraction for constants Integer and
  Fraction, supporting different ways of representing them
  internally. Additionally, this module provides several utility
  methods:

    * is_pysmt_fraction
    * is_pysmt_integer
    * is_python_integer
    * is_python_rational
    * is_python_boolean

  Conversion can be achieved via:

    * pysmt_fraction_from_rational
    * pysmt_integer_from_integer
    * to_python_integer (handle long/int py2/py3 mismatch)


* Add Version information (Issue #299 / PR #303)

  * pysmt.VERSION : A tuple containing the version information
  * pysmt.__version__ : String representation of VERSION (following PEP 440)
  * pysmt.git_version : A simple function that returns the version including git information.

  install.py (pysmt-install) and shell.py gain a new --version option that
  uses git_version to display the version information.


* Shortcuts: read_smtlib() and write_smtlib()

* Docs: Completely Revised the documentation (PR #294)

* Rewritings: TimesDistributor (PR #302)

  Perform distributivity on an N-ary Times across addition and
  subtraction.


* SizeOracle: Add MEASURE_BOOL_DAG measure (PR #319)

  Measure the Boolean size of the formula. This is equivalent to
  replacing every theory expression with a fresh boolean variable, and
  measuring the DAG size of the formula. This can be used to estimate
  the Boolean complexity of the SMT formula.


* PYSMT_SOLVERS controls available solvers (Issue #266 / PR #316):

  Using the PYSMT_SOLVER system environment option, it is possible to
  restrict the set of installed solvers that are actually accessible
  to pySMT. For example, setting PYSMT_SOLVER="msat,z3" will limit the
  accessible solvers to msat and z3.


* Protect FNodeContent.payload access (Issue #291 / PR 310)

  All methods in FNode that access the payload now check that the
  FNode instance is of the correct type, e.g.:

  FNode.symbol_name() checks that FNode.is_symbol()

  This prevents from accessing the payload in a spurious way. Since
  this has an impact on every access to the payload, it has been
  implemented as an assertion, and can be disabled by running the
  interpreter with -O.


Solvers:

* Z3 Converter Improvements (PR #321):

  * Optimized Conversion to Z3 Solver Forward conversion is 4x faster,
    and 20% more memory efficient, because we work at a lower level
    of the Z3 Python API and do not create intermediate AstRef objects
    anymore.  Back conversion is 2x faster because we use a direct
    dispatching method based on the Z3 OP type, instead of the
    big conditional that we were using previously.

  * Add back-conversion via SMT-LIB string buffer.
    Z3Converter.back_via_smtlib() performs back conversion by printing the
    formula as an SMT-LIB string, and parsing it back. For formulas of
    significant size, this can be drastically faster than using the API.

  * Extend back conversion to create new Symbols, if needed. This
    always raise a warning alerting the user that a new symbol is being
    implicitly defined.

* OSX: Z3 and MathSAT can be installed with pysmt-install (PR #244)

* MathSAT: Upgrade to 5.3.13 (PR #305)

* Yices: Upgrade to 2.5.1

* Better handling of solver options (PR  #338):

  Solver constructor takes the optional dictionary ``solver_options``
  of options that are solver dependent. It is thus possible to
  directly pass options to the underlying solver.


Bugfix:

* Fixed: Times back conversion in Z3 was binary not n-ary. Thanks to
  **Ahmed Irfan** for submitting the patch (PR #340, PR #341)

* Fixed: Bug in ``array_value_assigned_values_map``, returning the
  incorrect values for an Array constant value. Thanks to
  **Daniel Ricardo dos Santos** for pointing this out and submitting
  the patch.

* Fixed: SMT-LIB define-fun serialization (PR #315)

* Issue #323: Parsing of variables named bvX (PR #326)

* Issue #292: Installers: Make dependency from pip optional (PR #300)

* Fixed: Bug in MathSAT's ``get_unsat_core`` (PR #331), that could
  lead to an unbounded mutual recursion. Thanks to **Ahmed Irfan** for
  reporting this (PR #331)


0.5.1: 2016-08-17 -- NIRA and Python 3.5
----------------------------------------

Theories:

* Non Linear Arithmetic (NRA/NIA): Added support for
  non-linear, polynomial arithmetic. This thoery is currently
  supported only by Z3. (PR #282)

  * New operator POW and DIV

  * LIRA Solvers not supporting Non-Linear will raise the
    NonLinearError exception, while solvers not supporting arithmetics
    will raise a ConvertExpressionError exception (see
    test_nlira.py:test_unknownresult)

  * Algebraic solutions (e.g., sqrt(2) are represented using the
    internal z3 object -- This is bound to change in the future.


General:

* Python 3.5: Full support for Python 3.5, all solvers are now tested
  (and working) on Python 3.5 (PR #287)

* Improved installed solvers check (install.py)

  - install.py --check now takes into account the bindings_dir and
    prints the version of the installed solver

  - Bindings are installed in different directories depending on the
    minor version of Python. In this way it is possible to use both
    Python 2.7 and 3.5.

  - There is a distinction btw installed solvers and solvers in the
    PYTHONPATH.

  - Qelim, Unsat-Core and Interpolants are also visualized (but not
    checked)

* Support for reading compressed SMT-LIB files (.bz2)

* Simplified HRPrinter code

* Removed six dependency from type_checker (PR #283)

* BddSimplifier (pysmt.simplifier.BddSimplifier): Uses BDDs
  to simplify the boolean structure of an SMT formula. (See
  test_simplify.py:test_bdd_simplify) (PR #286)


Solvers:

* Yices: New wrapper supporting python 3.5 (https://github.com/pysmt/yicespy)
* Yices: Upgrade to 2.4.2
* SMT-LIB Wrapper: Improved interaction with subprocess (#298)

Bugfix:

* Bugfix in Z3Converter.walk_array_value. Thanks to **Alberto Griggio**
  for contributing this patch

* Bugfix in DL Logic comparison (commit 9e9c8c)


0.5.0: 2016-06-09 -- Arrays
---------------------------

BACKWARDS INCOMPATIBLE CHANGES:

* MGSubstituter becomes the new default substitution method (PR #253)

  When performing substitution with a mapping like ``{a: b, Not(a),
  c}``, ``Not(a)`` is considered before ``a``. The previous
  behavior (MSSubstituter) would have substituted ``a`` first, and
  then the rule for ``Not(a)`` would not have been applied.

* Removed argument ``user_options`` from Solver()

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

  Solver() takes ``**options`` as free keyword arguments. These options
  are checked by the class SolverOptions, in order to validate that
  these are meaningful options and perform a preliminary validation to
  catch typos etc. by raising a ValueError exception if the option is
  unknown.

  It is now possible to do: ``Solver(name="bdd", dynamic_reordering=True)``


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
