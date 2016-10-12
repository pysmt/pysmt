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

During a Pull-Request you will be asked to complete the form at CLAHub:
https://www.clahub.com/agreements/pysmt/pysmt . You will only have to
complete this once, but this applies to **all** your contributions.

If you are doing a drive-by patch (e.g., fixing a typo) and sending
directly a patch, you can skip the CLA, by sending a signed patch. A
signed patch can be obtained when committing using ``git commit -s``.

Tests
======

Running Tests
-------------

Tests in pySMT are developed using python's built-in testing framework
*unittest*.  Each *TestCase* is stored into a separate file,
and it should be possible to launch it by calling the file directly,
e.g.: ``$ python test_formula.py``.

However, the preferred way is to use nosetests, e.g.: ``$ nosetests pysmt/tests/test_formula.py``.

There are two utility scripts to simplify the testing of pysmt:
``run_tests.sh`` and ``run_all_tests.sh``.  They both exploit
additional options for nosetests, such as parallelism and
timeouts. ``run_all_tests.sh`` includes all the tests that are
marked as ``slow``, and therefore might take some time to complete.

Finally, tests are run across a wide range of solvers, versions of
python and operating systems using Travis CI.  This happens
automatically when you open a PR. If you want to run this before
submitting a PR, create a (free) Travis CI account, fork pySMT, and
enable the testing from Travis webinterface.

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

For convenience the script *make_distrib.sh* is provided, this builds
both the binary and source distributions within ``dist/``.

Building Documentation
======================

pySMT uses `Sphinx <http://www.sphinx-doc.org/en/stable/index.html/>`_ for documentation. To build the documentation you
will need `Sphinx <http://www.sphinx-doc.org/en/stable/index.html/>`_ installed, this can be done via pip.

A Makefile in the ``docs/`` directory allows to build the documentation in
many formats. Among them, we usually consider html and latex.
