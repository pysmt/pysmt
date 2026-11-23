.. _development:

===================
Developing in pySMT
===================

Licensing
=========

pySMT is distributed under the APACHE License (see LICENSE file). By
submitting a contribution, you automatically accept the conditions
described in LICENSE. Additionally, we ask you to certify that you have
the right to submit such contributions. We adopt the “Developer
Certificate of Origin” approach as done by the Linux kernel. ::

  Developer Certificate of Origin Version 1.1

  Copyright (C) 2004, 2006 The Linux Foundation and its contributors. 660
  York Street, Suite 102, San Francisco, CA 94110 USA

  Everyone is permitted to copy and distribute verbatim copies of this
  license document, but changing it is not allowed.

  Developer’s Certificate of Origin 1.1

  By making a contribution to this project, I certify that:

  (a) The contribution was created in whole or in part by me and I have
      the right to submit it under the open source license indicated in
      the file; or

  (b) The contribution is based upon previous work that, to the best of my
      knowledge, is covered under an appropriate open source license and I
      have the right under that license to submit that work with
      modifications, whether created in whole or in part by me, under the
      same open source license (unless I am permitted to submit under a
      different license), as indicated in the file; or

  (c) The contribution was provided directly to me by some other person
      who certified (a), (b) or (c) and I have not modified it.

  (d) I understand and agree that this project and the contribution are
      public and that a record of the contribution (including all personal
      information I submit with it, including my sign-off) is maintained
      indefinitely and may be redistributed consistent with this project
      or the open source license(s) involved.

During a Pull-Request you will be asked to edit the CONTRIBUTORS file to
add your name and email address. By doing so, you agree to the CLA.
You will only have to complete this once, but this applies to **all** your
contributions.

Development Setup
=================

pySMT uses `uv <https://docs.astral.sh/uv/>`_ to manage the development
environment and `just <https://just.systems/>`_ to run common tasks.
After installing both, run from the root of the repository::

  $ just install

This creates ``.venv`` with pySMT installed in editable mode and the
development dependencies pinned in ``uv.lock``. Running ``just`` without
arguments lists all the recipes:

* ``just install-solver NAME``: install a solver and check it (see below)
* ``just test`` and ``just test-all``: run the tests (see below)
* ``just lint``: check linting and formatting with ruff
* ``just format``: format the code and apply the automatic lint fixes
* ``just typecheck``: run mypy
* ``just precommit``: run all the pre-commit hooks on the whole repository
* ``just build``: build the sdist and the wheel into ``dist/``
* ``just docs``: build the HTML documentation into ``docs/_build/html``
* ``just bump VERSION``: set the version in ``pyproject.toml`` and
  refresh ``uv.lock``
* ``just clean``: remove build and cache directories

Dependencies are declared in ``pyproject.toml``. After changing them, run
``uv lock`` and commit the updated ``uv.lock``.

Solvers are installed in the same environment with ``pysmt-install``,
which uses ``uv pip`` since the environment has no pip::

  $ uv run pysmt-install --z3

``uv run`` keeps the installed solvers, but ``just install`` (``uv sync``)
removes every package that is not in ``uv.lock``, so solvers must be
installed again after it.

``just install-solver NAME`` installs a solver the way the CI does and
then runs ``pysmt-install --check`` to make sure that pySMT can use it::

  $ just install-solver msat
  $ just install-solver msat ~/my_solvers   # optional --install-path

NAME is a solver accepted by ``pysmt-install`` (e.g., ``z3``), ``all`` or
``none``. On Linux and macOS it can also be ``z3_wrap`` or ``msat_wrap``,
which copy the Z3 or MathSAT executable into ``tests/smtlib/bin``, where
the tests of the generic SMT-LIB wrapper find it, without installing the
Python bindings in the environment. ``all`` installs every solver and
copies both executables.

The recipe does not install OS packages. Z3, cvc5, Boolector and CUDD
(``bdd``) are installed from wheels, and Yices uses SRI's prebuilt binaries
on Linux x86_64 and macOS (elsewhere it is built from source). The other
solvers are built locally:

* MathSAT and OptiMathSAT need a C compiler and the gmp headers:
  ``libgmp-dev`` on Debian and Ubuntu, ``brew install gmp`` on macOS
  (with ``LIBRARY_PATH`` and ``CPATH`` pointing to the ``lib`` and
  ``include`` directories of ``brew --prefix``). On Windows
  ``pysmt-install`` downloads gmp itself and needs MSVC.
* PicoSAT needs a C compiler and swig.

On Windows, just runs the recipes with PowerShell, since ``bash`` may
resolve to the WSL launcher there.

Code Style
----------

pySMT uses `ruff <https://docs.astral.sh/ruff/>`_ for linting and
formatting, with a line length of 88 columns. The rules and the
exceptions are configured in ``pyproject.toml``. ``just format`` fixes
most issues, and ``just lint`` checks what the CI checks.

The pre-commit hooks run the linter, the type checker and a few file
checks before each commit. Enable them once per clone::

  $ uv run pre-commit install

The commit that reformatted the code base is listed in
``.git-blame-ignore-revs``. To make ``git blame`` skip it, run::

  $ git config blame.ignoreRevsFile .git-blame-ignore-revs

Tests
======

Running Tests
-------------

Tests in pySMT are developed using python's built-in testing framework
*unittest* and run with pytest::

  $ just test                                # skip slow tests, stop at the first failure
  $ just test-all                            # include the slow tests
  $ just test tests/test_formula.py          # run a single file

Extra arguments are passed to pytest. Tests that take more than 10
seconds should be marked with ``@pytest.mark.slow``.

Finally, tests are run across a wide range of solvers, versions of
python and operating systems using GitHub Actions. The workflow
``.github/workflows/ci-pr.yml`` runs on every PR: it runs ``just lint``
and ``just typecheck``, then a matrix of jobs defined by the reusable
workflow ``.github/workflows/test.yml``. Each job runs ``just
install-solver NAME`` and ``just test-all``. The matrix covers every
solver on Linux with Python 3.14, Python 3.10 to 3.13 without solvers,
gmpy2 and Cython, and a subset of the solvers on macOS and Windows. The
``all`` job also runs the scripts in ``examples/``. If you want to run
the CI before submitting a PR, enable GitHub Actions on your fork of
pySMT, push your branch there and start the *CI-on-PR* workflow from the
Actions tab.

All tests should pass for a PR to be merged.

Writing Tests
-------------

The tests live in the top-level ``tests/`` directory, which is not part
of the installed package. Test cases should inherit from ``TestCase``,
defined in ``tests/__init__.py`` and imported with ``from tests import
TestCase``. Its ``setUp`` method resets the global environment before
each test, which avoids interactions between tests. The class also
provides the assertions ``assertValid``, ``assertSat`` and
``assertUnsat``, which check a formula using the solver factory of the
test environment.

``tests/__init__.py`` also defines decorators, such as
``skipIfSolverNotAvailable`` and ``skipIfNoSolverForLogic``, that skip
a test when the solver it needs is not installed.

PYSMT_SOLVER
~~~~~~~~~~~~

The system environment variable ``PYSMT_SOLVER`` controls which
solvers are actually available to pySMT. When developing it is common
to have multiple solvers installed, but wanting to only test on few of
them. For this reason ``PYSMT_SOLVER`` can be set to a list of
solvers, e.g., ``PYSMT_SOLVER="msat, z3"`` will provide access to
pySMT only to msat and z3, independently of which other solvers are
installed. If the variable is unset or set to ``all``, it does not
have any effect.

How to add a new Theory within pySMT
====================================

In pySMT we are trying to closely follow the SMT-LIB standard. If the
theory you want to add is already part of the standard, than many
points below should be easy to answer.

1. Identify the set of operators that need to be added
    You need to distinguish between operators that are needed to represent
    the theory, and operators that are syntactic sugar. For example, in
    pySMT we have less-than and less-than-equal, as basic operators, and
    define greater-than and greater-than-equal as syntactic sugar.

2. Identify which solvers support the theory
    For each solver that supports the theory, it is important to identify
    which sub/super-set of the operators are supported and whether the
    solver is already integrated in pySMT. The goal of this activity is to
    identify possible incompatibilities in the way different solvers deal
    with the theory.

3. Identify examples in "SMT-LIB" format
    This provides a simple way of looking at how the theory is used, and
    access to cheap tests.

Once these points are clear, please open an issue on github with the
answer to these points and a bit of motivation for the theory. In this
way we can discuss possible changes and ideas before you start working
on the code.

Code for a new Theory
---------------------

A good example of theory extension is represented by the BitVector
theory. In case of doubt, look at how the BitVector case (bv) has been
handled.

Adding a Theory to the codebase is done by following these steps:

1. Tests: Add a test file ``tests/test_<theory>.py``, to demonstrate the use for the theory (e.g., ``tests/test_bv.py``).

2. Operators: Add the (basic) operators in ``src/pysmt/operators.py``, create a constant for each operator, and extend the relevant structures.

3. Typing: Extend ``src/pysmt/typing.py`` to include the types (sorts) of the new theory.

4. Walker: Extend ``src/pysmt/walkers/generic.py`` to include one ``walk_`` function for each of the basic operators.

5. FNode: Extend ``is_*`` methods in :py:class:`pysmt/fnode.py:FNode`. This makes it possible to check the type of an expression, obtaining additional elements (e.g., width of a bitvector constant).

6. Typechecker: Extend :py:class:`pysmt/type_checker.py:SimpleTypeChecker` to include type-checking rules.

7. FormulaManager: Create constructor for all operators, including syntactic sugar, in :py:class:`pysmt/formula.py:FormulaManager`.

At this point you are able to build expressions in the new
theory. This is a good time to start running your tests.

8. Printers: Extend :py:class:`pysmt/printers.py:HRPrinter` to be able to print expressions in the new theory (you might need to do this earlier, if you need to debug your tests output).

9. Examples: Extend ``tests/examples.py`` with at least one example formula for each new operator defined in FormulaManager. These examples are used in many tests, and will help you identify parts of the system that still need to be extended (e.g., Simplifier).

10. Theories and Logics: Extend ``src/pysmt/logics.py`` to include the new Theory and possible logics that derive from this Theory. In particular, define logics for each theory combination that makes sense.

11. SMT-LIB: Extend :py:class:`pysmt/smtlib/parser.py:SmtLibParser` and ``src/pysmt/smtlib/printers.py`` to support the new operators.

12. Shortcuts: All methods that were added in FormulaManager need to be available in ``src/pysmt/shortcuts.py``.

At this point all pySMT tests should pass. This might require
extending other walkers to support the new operators.

13. Solver: Extend at least one solver to support the Logic. This is done by extending the associated Converter (e.g., :py:class:`pysmt/solvers/msat.py:MSatConverter`) and adding at least one logic to its ``LOGICS`` field. As a bare-minimum, this will require a way of converting solvers-constants back into pySMT constants (``Converter.back()``).

Packaging and Distributing PySMT
================================

Packages are built with `hatchling <https://hatch.pypa.io/>`_, configured
in ``pyproject.toml``. The command ``just build`` produces the sdist and the
wheel inside the ``dist/`` directory.

Building Documentation
======================

pySMT uses `Sphinx <http://www.sphinx-doc.org/en/stable/index.html/>`_
for documentation. ``just docs`` builds the HTML documentation into
``docs/_build/html``; Sphinx runs in a temporary environment through
``uvx``, so it does not need to be installed.

Preparing a Release (Check-List)
================================

In order to make a release, the master branch must pass all tests on
the CI (GitHub Actions). The release process is broken down into the
following steps:

 * Release branch creation
 * Changelog update
 * Version change
 * Package creation and local testing
 * Merge
 * Tag (publishes to PyPI and creates the GitHub Release)
 * Version Bumping
 * Announcement

Every push to master and every ``v*`` tag runs
``.github/workflows/build-and-release.yml``. It runs the same checks as
a PR, builds the package with ``just build`` and uploads it to PyPI
through trusted publishing:

* On master, ``ci/stamp_dev_version.py`` replaces the ``.dev0`` suffix of
  the version in ``pyproject.toml`` with ``.devN``, where N is the total
  number of commits, and the ``.devN`` build is uploaded. A release
  version on master (the merge of a release branch) is built but not
  uploaded.
* On a tag ``va.b.c``, the workflow checks that the version in
  ``pyproject.toml`` is ``a.b.c``, uploads it to PyPI and creates the
  GitHub Release ``va.b.c`` with the sdist and the wheel attached.

PyPI does not allow re-uploading a version, so pushing the tag is the
point of no return: everything must be checked before that.


Release Branch Creation
-----------------------

As all other activities, the creation of a release requires
working on a separate branch. This makes it possible to interrupt,
share, and resume the release creation, if bugs are discovered during
this process. The branch must be called ``rc/a.b.c``, where a.b.c is
the version number of the target release.


Changelog Update (docs/CHANGES.rst)
-----------------------------------

Use ``git log`` to obtain the full list of commits from the latest
tag. We use merge commits to structure the Changelog, however,
sometimes additional and useful information is described in
intermediate commits, and it is thus useful to have them.

The format of the header is ``<version>: <year> -- <Title>``, where
version has the format Major.Minor.Patch (e.g., 0.6.1) and year is in
ISO format: YYYY-MM-DD (e.g., 2016-11-28). The title should be brief
and possible include the highlights of the release.

The body of the changelog should start with the backwards incompatible
changes with a prominent header. The other sections (optional if
nothing changed) are:

* General: For new features of pySMT
* Solvers: For upgrades or improvements to the solvers
* Theories: For new or improved Theories
* Bugfix: For all the fixes that do not constitute a new feature

Each item in the lists ends with reference to the Github issue or Pull
request. If an item deserves more explanation and it is not associated
with an issue or PR, it is acceptable to point to the exact commit
id).  Items should also acknowledge contributors for submitting
patches, opening tickets or simply discussing a problem.

The changelog ends with the list of new contributors and a link to the
full diff. GitHub computes the list of new contributors::

  gh api repos/pysmt/pysmt/releases/generate-notes \
     -f tag_name=va.b.c -f target_commitish=master \
     -f previous_tag_name=v<previous> --jq .body

Version change
--------------

Set the version in ``pyproject.toml`` with ``just bump a.b.c`` (e.g.,
``just bump 0.6.1``), which also refreshes ``uv.lock``.

Package creation and local testing
----------------------------------

``just build`` creates the sdist (``dist/pysmt-a.b.c.tar.gz``) and the wheel.
Build them from a clean checkout of the release branch (e.g., with
``git worktree add``), so that untracked files in your working copy do
not end up in the package.

Before merging, we test the package locally, to make sure that
everything works. The most common mistake in this phase is the
omission of a file in the package. Install it in a fresh virtual
environment and run a copy of the tests against it, from a directory
that does not contain the ``pysmt`` sources:

 0. ``python3 -m venv venv && . venv/bin/activate``
 1. ``pip install pytest dist/pysmt-a.b.c.tar.gz``
 2. ``mkdir test_pkg && cp -a <repo>/tests test_pkg/``
 3. ``cd test_pkg && python -m pytest tests``

Check that pytest imports pysmt from ``venv`` and not from a source
tree. All tests should pass in order to make the release. Note: It is
enough to have one solver installed, in order to test the package. The
type of issues that might occur during package creation are usually
independent of the solver.


Merge
-----

Open a PR from ``rc/a.b.c`` to master and merge it once the CI is
green. The merge commit is built but not uploaded to PyPI.


Tag
---

Tag the merge commit with ``git tag -a va.b.c`` (note the ``v`` before
the major version number), and push the tag to GitHub with ``git push
origin va.b.c``. The ``build-and-release`` workflow on the tag runs the
tests, uploads ``a.b.c`` to PyPI and creates the GitHub release with
the published wheel and tar.gz attached.

Once the workflow is green, check that https://pypi.org/project/pysmt/a.b.c/
exists, and replace the generated description of the GitHub release
with the Changelog of the release.


Version Bumping
---------------

Immediately after tagging, make a commit on master bumping the
version. By default we use ``just bump a.b.(c+1).dev0``.


Announcement
------------

* Mailing list: https://groups.google.com/forum/#!forum/pysmt
* Make sure the Github Release has been created


Performance Tricks
==================

It is our experience that in many cases the performance limitations
come from the solvers or from a sub-optimal encoding of the problem,
and that pySMT performs well for most use-cases. Nevertheless,
sometimes you just want to squeeze a bit more performance from the
library, and there are a few things that you might want to try. As
always, you should make sure that your code is correct before starting
to optimize it.

Disable Assertions
------------------

Run the python interpreter with the ``-O`` option. Many functions in
pySMT have assertions to help you discover problems early on. By using
the `command line option
<https://docs.python.org/3/using/cmdline.html?highlight=#cmdoption-O>`_
``-O`` all assertions are disabled


Avoid Infix Notation and shortcuts
----------------------------------

Infix notation and shortcuts assume that you are operating on the
global environment. The expression ``a & b`` needs to:

1. Resolve the implicit operator (i.e., translate ``&`` into ``And``)
2. Access the global environment
3. Access the corresponding formula manager
4. Check if the right-hand-side is already an FNode
5. Call ``FormulaManager.And`` on the two elements.

Using a shortcut is similar in complexity, although you skip step 1
and 4. Therefore, within loop intensive code, make sure that you
obtain a reference to the current formula manager or even better to
the actual function call that you want to perform: e.g., ::

  Real = get_env().formula_manager.Real
  for x in very_large_set:
      Real(x)

This will save dereferencing those objects over-and-over again.


Disabling Type-Checking
-----------------------

If you really want to squeeze that extra bit of performance, you might
consider disabling the type-checker. In pySMT all expressions are
checked at creation time in order to guarantee that they are
well-formed and well-typed. However, this also means that on very big
expressions, you will call many times the type-checker (see discussion
in `#400 <https://github.com/pysmt/pysmt/pull/400>`_). Although, all
calls to the type-checker are memoized, the cost of doing so can add
up. If you are 100% sure that your expressions will be well-typed,
then you can use the following code to create a context that disables
temporarily the type-checker. WARNING: If you create an expression
that is not well-typed while the type-checker is disabled, there is no
way to detect it later on. ::

  class SuspendTypeChecking(object):
      """Context to disable type-checking during formula creation."""

      def __init__(self, env=None):
          if env is None:
              env = get_env()
          self.env = env
          self.mgr = env.formula_manager

      def __enter__(self):
          """Entering a Context: Disable type-checking."""
          self.mgr._do_type_check = lambda x : x
          return self.env

      def __exit__(self, exc_type, exc_val, exc_tb):
          """Exiting the Context: Re-enable type-checking."""
          self.mgr._do_type_check = self.mgr._do_type_check_real

This can be used as follows: ::


  with SuspendTypeChecking():
      r = And(Real(0), Real(1))


PyPy
----

pySMT is compatible with `pypy <http://pypy.org>`_. Unfortunately, we
cannot run most of the solvers due to the way the bindings are created
today. However, if are interfacing through the SMT-LIB interface, or
are not using a solver, you can run pySMT using pypy. This can
drastically improve the performances of code in which most of the time
is spent in simple loops. A typical example is parsing, modifying, and
dumping an SMT-LIB: this flow can significantly improve by using pypy.

Some work has been done in order to use `CFFI
<http://cffi.readthedocs.io/en/latest/>`_ to interface more
solvers with pypy (see `mathsat-cffi
<https://github.com/pysmt/mathsat-cffi>`_ repo). If you are interested
in this activity, please `get in touch <https://groups.google.com/forum/#!forum/pysmt>`_.
