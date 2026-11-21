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

Tests
======

Running Tests
-------------

Tests in pySMT are developed using python's built-in testing framework
*unittest*.  Each *TestCase* is stored into a separate file,
and it should be possible to launch it by calling the file directly,
e.g.: ``$ python test_formula.py``.

However, the preferred way is to use pytest, e.g.: ``$ python -m pytest pysmt/tests/test_formula.py``.

There are two utility scripts to simplify the testing of pysmt:
``run_tests.sh`` and ``run_all_tests.sh``.  They both exploit
additional options for pytest, such as timeouts. ``run_all_tests.sh``
includes all the tests that are marked as ``slow``, and therefore
might take some time to complete.

Finally, tests are run across a wide range of solvers, versions of
python and operating systems using GitHub Actions. This happens
automatically when you open a PR. If you want to run this before
submitting a PR, enable GitHub Actions on your fork of pySMT and push
your branch there.

All tests should pass for a PR to be merged.

Writing Tests
-------------

TestCase should inherit from :py:class:`pysmt.test.TestCase`.  This
provides a default :py:meth:`~pysmt.test.TestCase.SetUp` for running
tests in which the global environment is reset after each test is
executed. This is necessary to avoid interaction between
tests. Moreover, the class provides some additional assertions:

.. autoclass:: pysmt.test.TestCase

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

1. Tests: Add a test file ``pysmt/test/test_<theory>.py``, to demonstrate the use for the theory (e.g., ``pysmt/test/test_bv.py``).

2. Operators: Add the (basic) operators in ``pysmt/operators.py``, create a constant for each operator, and extend the relevant structures.

3. Typing: Extend ``pysmt/typing.py`` to include the types (sorts) of the new theory.

4. Walker: Extend ``pysmt/walkers/generic.py`` to include one ``walk_`` function for each of the basic operators.

5. FNode: Extend ``is_*`` methods in :py:class:`pysmt/fnode.py:FNode`. This makes it possible to check the type of an expression, obtaining additional elements (e.g., width of a bitvector constant).

6. Typechecker: Extend :py:class:`pysmt/type_checker.py:SimpleTypeChecker` to include type-checking rules.

7. FormulaManager: Create constructor for all operators, including syntactic sugar, in :py:class:`pysmt/formula.py:FormulaManager`.

At this point you are able to build expressions in the new
theory. This is a good time to start running your tests.

8. Printers: Extend :py:class:`pysmt/printers.py:HRPrinter` to be able to print expressions in the new theory (you might need to do this earlier, if you need to debug your tests output).

9. Examples: Extend ``pysmt/test/examples.py`` with at least one example formula for each new operator defined in FormulaManager. These examples are used in many tests, and will help you identify parts of the system that still need to be extended (e.g., Simplifier).

10. Theories and Logics: Extend ``pysmt/logics.py`` to include the new Theory and possible logics that derive from this Theory. In particular, define logics for each theory combination that makes sense.

11. SMT-LIB: Extend :py:class:`pysmt/smtlib/parser.py:SmtLibParser` and ``pysmt/smtlib/printers.py`` to support the new operators.

12. Shortcuts: All methods that were added in FormulaManager need to be available in ``pysmt/shortcuts.py``.

At this point all pySMT tests should pass. This might require
extending other walkers to support the new operators.

13. Solver: Extend at least one solver to support the Logic. This is done by extending the associated Converter (e.g., :py:class:`pysmt/solvers/msat.py:MSatConverter`) and adding at least one logic to its ``LOGICS`` field. As a bare-minimum, this will require a way of converting solvers-constants back into pySMT constants (``Converter.back()``).

Packaging and Distributing PySMT
================================

The setup.py script can be used to create packages. The command

``python setup.py bdist --format=gztar``

will produce a tar.gz file inside the ``dist/`` directory.

For convenience the script ``make_distrib.sh`` is provided, this builds
both the binary and source distributions within ``dist/``.

Building Documentation
======================

pySMT uses `Sphinx <http://www.sphinx-doc.org/en/stable/index.html/>`_
for documentation. To build the documentation you will need Sphinx
installed, this can be done via pip.

A Makefile in the ``docs/`` directory allows to build the documentation in
many formats. Among them, we usually consider html and latex.

Preparing a Release (Check-List)
================================

In order to make a release, the master branch must pass all tests on
the CI (GitHub Actions). The release process is broken down into the
following steps:

 * Release branch creation
 * Changelog update
 * Version change
 * Package creation and local testing
 * Merge (publishes to PyPI)
 * Tag and GitHub Release
 * Version Bumping
 * Announcement

Every push to master runs the ``deploy-pypi`` job in
``.github/workflows/test.yml``, which builds the package with
``make_distrib.sh`` and uploads it to PyPI. On development versions
(``VERSION`` ending in ``"dev", 1``) this uploads a ``.devN`` build. On
a release version it uploads the release itself. PyPI does not allow
re-uploading a version, so merging the release branch is the point of
no return: everything must be checked before that.


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

The variable ``VERSION`` in ``pysmt/__init__.py`` must be modified to
show the correct version number: e.g., ``VERSION = (0, 6, 1)``.

Package creation and local testing
----------------------------------

The utility script ``make_distrib.sh`` in the root directory of the
project creates the sdist (``dist/pysmt-a.b.c.tar.gz``) and the wheel.
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
 2. ``mkdir -p test_pkg/pysmt && cp -a <repo>/pysmt/test test_pkg/pysmt/``
 3. ``cd test_pkg && python -m pytest pysmt/test``

Check that pytest imports pysmt from ``venv`` and not from a source
tree. All tests should pass in order to make the release. Note: It is
enough to have one solver installed, in order to test the package. The
type of issues that might occur during package creation are usually
independent of the solver.


Merge
-----

Open a PR from ``rc/a.b.c`` to master and merge it once the CI is
green. The ``deploy-pypi`` job on the merge commit uploads ``a.b.c``
to PyPI. Check that https://pypi.org/project/PySMT/a.b.c/ exists
before continuing. Do not merge anything else into master until the
version has been bumped (see below), otherwise the CI tries to upload
``a.b.c`` again and fails.


Tag and GitHub Release
----------------------

Tag the merge commit with ``git tag -a va.b.c`` (note the ``v`` before
the major version number), and push the tag to GitHub with ``git push
origin va.b.c``.

Then create the GitHub release associated with this tag. The
description of the release is the copy-paste of the Changelog.
Additionally, we attach the wheel and the tar.gz downloaded from PyPI,
so that they are exactly the published files.


Version Bumping
---------------

Immediately after tagging, make a commit on master bumping the
version. By default we use ``(a, b, c+1, "dev", 1)``.


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
