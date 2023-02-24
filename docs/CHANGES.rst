Change Log
==========

0.9.5: 2022-05-28 -- 2 years of bugfixes
----------------------------------------

Intermediate release that collects 2 years of bugfixes and improvements.

Python 2 was deprecated in version 0.9.0, and this version removes the use of compatible code for that version.

## What's Changed

* Add support for boolean-typed array in the AtomsOracle by @mikand in https://github.com/pysmt/pysmt/pull/644
* Switched from nosetests to pytest by @mikand in https://github.com/pysmt/pysmt/pull/662
* Fixed a bug in yices quantifier support and added regression test by @mikand in https://github.com/pysmt/pysmt/pull/657
* Fix Boolector install script by @4tXJ7f in https://github.com/pysmt/pysmt/pull/656
* BUG: define UFNIA as logic with integer arithmetic by @johnyf in https://github.com/pysmt/pysmt/pull/659
* Handling of algebraic constants in simplify by @EnricoMagnago in https://github.com/pysmt/pysmt/pull/658
* Integer div by @EnricoMagnago in https://github.com/pysmt/pysmt/pull/667
* Fix CVC4 installation on macOS by @kammoh in https://github.com/pysmt/pysmt/pull/666
* Bug in times distributor by @EnricoMagnago in https://github.com/pysmt/pysmt/pull/671
* Fixed reset_assertion method for incremental-tracking solvers by @mikand in https://github.com/pysmt/pysmt/pull/672
* Minor Corrections by @mfarif in https://github.com/pysmt/pysmt/pull/673
* implement add_assertions method for solver. by @EnricoMagnago in https://github.com/pysmt/pysmt/pull/679
* Fix "get_model" when called from a generic solver (Fix #674) by @btwael in https://github.com/pysmt/pysmt/pull/675
* Remove six and python 2 compatibility code by @marcogario in https://github.com/pysmt/pysmt/pull/684
* Added fallback to Swig3 to address as much as possible issue #682 by @mikand in https://github.com/pysmt/pysmt/pull/685
* Fix to correctly pass logic to solvers started by Portfolio by @ekilmer in https://github.com/pysmt/pysmt/pull/683
* SmtLib model validation support by @mikand in https://github.com/pysmt/pysmt/pull/681
* Fix iss694 by @EnricoMagnago in https://github.com/pysmt/pysmt/pull/695
* Fixed CVC4 installer after upstream repository renaming by @mikand in https://github.com/pysmt/pysmt/pull/697
* Remove call to `FNode.substitute` in SmtLibExecutionCache by @EnricoMagnago in https://github.com/pysmt/pysmt/pull/699
* Added printing of annotations to smt lib printers by @agirardi-fbk in https://github.com/pysmt/pysmt/pull/703
* Integer div by @EnricoMagnago in https://github.com/pysmt/pysmt/pull/705
* Updated docker images to solve deprecation issue on azure pipelines by @mikand in https://github.com/pysmt/pysmt/pull/706
* Workaround to fix Z3 segfault by @mikand in https://github.com/pysmt/pysmt/pull/713
* Add possibility to use several BV operators as left associative by @agirardi-fbk in https://github.com/pysmt/pysmt/pull/714
* Fixed issue #613 by @mikand in https://github.com/pysmt/pysmt/pull/710

## New Contributors
* @4tXJ7f made their first contribution in https://github.com/pysmt/pysmt/pull/656
* @johnyf made their first contribution in https://github.com/pysmt/pysmt/pull/659
* @kammoh made their first contribution in https://github.com/pysmt/pysmt/pull/666
* @mfarif made their first contribution in https://github.com/pysmt/pysmt/pull/673
* @btwael made their first contribution in https://github.com/pysmt/pysmt/pull/675
* @ekilmer made their first contribution in https://github.com/pysmt/pysmt/pull/683
* @agirardi-fbk made their first contribution in https://github.com/pysmt/pysmt/pull/703

**Full Changelog**: https://github.com/pysmt/pysmt/compare/v0.9.0...v0.9.5

0.9.0: 2020-04-26 -- PySMT as module
------------------------------------

General:

* PySMT as module (PR #573): It is now possible to do
    python -m pysmt install

  and

    python -m pysmt shell

  while the tool pystm-install is still available, using the module syntax makes it easier to understand which version of python will be used, in case multiple interpreters co-exist.

* Added functions to obtain the symbols in SMTLIB script (PR #583)

* Python 2 is not supported anymore. While it might still work, we will not actively test for it anymore.

Solvers:

* Boolector: Incremental and Unsat cores support (PR #591, #567). Thanks **Makai Mann** for providing the patch.

* Picosat: Fixed a bug related to solver reset (PR #567)

* Boolector: Upgrade to 3.2.1

* MathSAT: Upgrade to 5.6.1

Bugfix:

* Collections.abc: fix deprecation warning (PR #574, PR #562). Thanks to **Liana Hadarean** and **Caleb Donovick**.

* PysmtSyntaxError: Fix missing message constructor (PR #576). Thanks to **Liana Hadarean** for providing a fix.

* Version: Static version in make_distrib.sh (PR #575)

* Fix simplifier StrIndexOf capitalization (PR #563). Thanks to **Makai Mann** for providing the patch.

* Sort the arguments of Times while simplifying (PR #561). Thanks to **Ahmed Irfan** for providing the patch.

* Fix bug in deque pop in smtlib/parser (PR #558). Thanks to **Sebastiano Mariani** for providing the patch.

* Function names quoted with `'` instead of `|` when seraializing to smt2 (PR #584). Thanks **Kevin Laeufer** for reporting this.

* Fix assertion tracking for boolector (PR #589). Thanks **Makai Mann** for providing the patch.

* Handle one-bit shifts in btor (PR #592) Thanks **Makai Mann** for providing the patch.

* Fix issue with bv conversion in Yices (PR #597). Thanks to `@nano-o` for reporting this.

* Fix Mathsat signature for BV_CONCAT (PR #598). Thanks **Makai Mann** for providing the patch.

* Support n-ary BVConcat (PR #621). Thanks to **Ridwan Shariffdeen** for reporting this.

* Fix a correctness issue when reading from SMT-LIB interface (Issue #616, #615, PR #619). Thanks to **Sergio Mover** for reporting this.

* Clear pending assertions in IncrementalTrackingSolver.assertions (PR #627). Thanks to **Enrico Magnago** for reporting this.

* Various documentation fixes. Thanks to **Matthew Fernandez**, **Guillem Francès**, and **Gianluca Redondi**.

* Disable multiprocessing in run_tests.sh script (PR #637). Thanks **Patrick Trentin** for reporting this.

0.8.0: 2019-01-27 -- Better Install and Great Community
-------------------------------------------------------

BACKWARDS INCOMPATIBLE CHANGES:

  Disabled support for interpolation in Z3, since this is not
  available anymore up-stream

Deprecation Warning:

This release is the **last** release to support Python 2.7.
Starting from 0.9.0 only Python 3+ will be supported.

General:

* Solver installation within site-package (PR #517). pysmt-install now
  installs the solvers within the site-package directory (by
  default). This makes it possible to work with virtual environments,
  and does not require anymore to export the Python path, greatly
  simplifying the installation process. Thanks to **Radomir
  Stevanovic** for contributing the patch.

* Simplify shared lib usage (PR #494): Modify z3 and msat installers
  in order to make their shared binary objects (libraries/dlls)
  auto-discoverable, without the need for setting
  LD_LIBRARY_PATH/PATH. Thanks to **Radomir Stevanovic** for
  contributing the patch.

* BV Simplification (PR #531): Multiple improvements on the
  simplification of BV expressions. Thanks to **Haozhong Zhang** for
  contributing the patch.

* Ackermannization (PR #515): Add support for Ackermannization in
  pysmt.rewritings. Thanks to **Yoni Zohar** for contributing the patch.

* FNode.bv_str: Multiple format for BV printing (PR #468)

* Examples (PR #507): Extend model_checking example with PDR. Thanks
  to **Cristian Mattarei** for contributing the patch.

* Docs: Tutorial on basic boolean solving (PR #535)

* Tests: Removed old warning and other clean-ups (PR #532, #512)

* Warnings (PR #497): Importing pysmt.shortcuts will only raise
  warnings within pySMT, instead of all warnings from external
  libraries.

* Examples (PR #541): Add example for the theory of Strings

* Top-Level Propagator (PR #544): Add a basic toplevel-propagation
  functionality to propagate definitions of the form: variable =
  constant, variable = variable, constant = constant .
  Thanks to **Ahmed Irfan** for providing this feature.

* Clean-up debug print from SMT parser (PR #543): Thanks to **Ahmed
  Irfan** for providing this patch.


Solvers:

* Yices: Upgrade to 2.6.0 (PR #509).

* Boolector: Upgrade to 3.0.1-pre (7f5d32) (PR #514)

* CVC4: Upgrade to 1.7-prerelease (PR #552)
  *Known issue*: Passing options to CVC4 fails sometimes.

* Z3: Upgrade to 4.8.4 (PR #550).
  Removed support for interpolation.
  *Known issue*: Some tests on use of tactics exhibit some random
   failures on Travis.

* Yices: Add support for OSX (PR #486). Thanks to **Varun Patro** for
  contributing the patch.

* SMTLIB Solver (PR #524): Add support for custom sorts in SMT-LIB
  interface. Thanks to **Yoni Zohar** for contributing the patch.

* MathSAT (PR #526): Add option to support preferred variables with
  polarity. Thanks to **Cristian Mattarei** for providing the patch.


Bugfix:

* SmtLib parser (PR #521): Fix StopIteration error. The error would
  make it impossible to use the parser with Python 3.7. The fix
  changes the structure of the parser, in order to separate cases in
  which we know that there is a token to consume (function consume)
  and when we want to consume a token only if available (function
  consume_maybe). Thanks to **@samuelkolb** and **Kangjing Huang** for
  reporting this.

* Boolector: Fixed bug in LShl and LShr conversion (PR #534)

* Z3 (PR #530, #528): Fixed race condition during context
  deletion. The race condition would cause pySMT to segfault on
  certain situations. Thanks to **Haozhong Zhang** for helping us
  reproduce the issue and to **@Johanvdberg** for reporting it.

* MathSAT (PR #518): Fix installation error on darwin. Thanks to
  **Lenny Truong** for contributing the patch.

* Fix declare-sort bug (PR #501). Thanks to **Yoni Zohar** for
  contributing the patch.

* Fix docstring for BVAShr (PR #503). Thanks to **Mathias Preiner**
  for contributing the patch.

* Fix yices compilation on OSX without AVX2 instruction (PR #491)

* Fix PysmtTypeError when reusing symbols in SMT-LIB define-fun (PR
  #502). Thanks to **Yoni Zohar** for contributing the patch.

* Fix doublequote escaping (PR #489). Thanks to **Lukas Dresel** for
  contributing the patch.

* Fix pySMT CLI for Python3 (PR #493). Thanks to **Radomir
  Stevanovic** for contributing the patch.


0.7.5: 2018-05-29 -- Strings and Cython Parser
----------------------------------------------

General:
* Strings Theory (#458)

  Add support for the theory of Strings as supported by CVC4.

  Direct solver support is limited to CVC4, but the SMT-LIB interface
  can be used to integrate with other solvers (e.g., Z3).

  This feature was largely implemented by **Suresh Goduguluru** and
  motivated by **Clark Barrett**.


* SMT-LIB Parser: Improved performance with Cython (PR #432)

  The SMT-LIB parser module is now compiled using Cython behind the
  scenes. By default pySMT will try to use the cython version but the
  behavior can be controlled via env variables::

    PYSMT_CYTHON=False # disable Cython
    PYSMT_CYTHON=True  # force Cython: Raises an error if cython or the
                       # SMT-LIB parser module are not available.
    unset PYSMT_CYTHON # defaults to Cython but silently falls back to
                       #pure-python version

  The API of ``pysmt.smtlib.parser`` does not change and preserves
  compatibility with previous versions.

  Benchmarking on parse_all.py shows: ::

    $ PYSMT_CYTHON=True python3.5 parse_all.py --count 500
    The mean execution time was 2.34 seconds
    The max execution time was 59.77 seconds

    $ PYSMT_CYTHON=False python3.5 parse_all.py --count 500
    The mean execution time was 3.39 seconds
    The max execution time was 85.46 seconds

* SMT-LIB Parser: Added Debugging Information (Line/Col number) (PR #430)

* pysmt-install: Simplified solver version check (PR #431)

* Extended infix notation to support:
  - Store and Select (PR #437)
  - NotEquals (PR #438)
  - EUF Function application (PR #445)

* Examples: Quantifier Elimination in LRA (PR #447)

* Sorts: Stronger type checking for composite sorts (PR #449)

* BvToNatural: Introduced new operator to convert bitvectors into
  natural numbers (PR #450)

* Examples: Theory Combination (PR #451)

* QE: Introduce new QE techniques based on Self-Substitution (PR #460)


Solvers:
* Z3: Upgrade to 4.5.1 dev (082936bca6fb) (PR #407)

* CVC4: Upgrade to 1.5 (PR #424)

* MathSAT: Upgrade to 5.5.1 (PR #453)

* MathSAT: Add Windows Support (PR #453)


Theories:
* Support for Theory of Strings (SMT-LIB + CVC4) (PR #458)


Bugfix:

* Z3: Conversion of top-level ITE (PR #433)

* Z3: Fixed exception handling (PR #473): Thanks to **Bradley Ellert**
  for reporting this.

* Detect BV type in Array and Function when using infix notation (PR #436)

* Support GMPY objects in BV construction (PR #441)

* SMT-LIB: Fixed parsing of #x BV constants (PR #443): Thanks to
  **@cdmcdonell** for reporting this.

* SMT-LIB: Remove trailing whitespace from bvrol and bvsext (PR #459)

* Fixed type-checking of Equals, LT and LE (PR #452)

* Examples: Revised Einstein example (PR #448): Thanks to **Saul
  Fuhrmann** for reporting the issue.

* Examples: Fixed indexing and simple path condition in MC example (PR
  454): Thanks to **Cristian Mattarei** for contributing this patch.

* Fixed installer for picosat to use HTTPS (PR #481)


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
