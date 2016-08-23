.. _development:

===================
Developing in pySMT
===================

Building Documentation
======================

pySMT uses Sphinx for documentation. To build the documentation you
will need sphinx installed, this can be done via pip.

A Makefile in the docs/ directory allows to build the documentation in
many formats. Among them, we usually consider html and latex.

Tests
======

Running Tests
-------------

Tests in pySMT are developed using python's built-in testing framework
unittest. Each TestCase is stored into a separate file, and it should
be possible to launch it by calling the file directly, e.g.:

``python test_formula.py``

This is useful to run the debugger within a test.

To launch all the tests, scripts *run_tests.sh* and *run_all_tests.sh* are
provided. We strive to keep the execution time of the tests
brief. *run_tests.sh* should complete within 1 minute. To achieve
this, we use parallel tests, and we skip slow tests. To run all tests,
use *run_all_tests.sh* this usually takes significantly longer (3 minutes).
This depends heavily on which solvers you have installed. Both
scripts run internally *nosetest*. Therefore, you can run a single set
of tests with:

``nosetests pysmt/tests/test_formula.py``

Writing Tests
-------------

TestCase should inherit from :class:`pysmt.test.TestCase`. This class
extends the basic TestCase class in two ways. First, it provides
additional assertions [[TODO: Document assertIsSAT etc]].
Second, it provides a default SetUp for running tests in which the
global environment is reset after each test is executed. This is
necessary to avoid interaction between tests.


Distributing PySMT
==================

The setup.py script can be used to create packages. The command

``python setup.py bdist --format=gztar``

will produce a tar.gz file inside the ``dist/`` directory.

For convenience the script *make_distrib.sh* is provided, this builds
both the binary and source distributions within ``dist/``.
