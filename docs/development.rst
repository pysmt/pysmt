Developing in pySMT
===================

Building Documentation
----------------------
pySMT uses Sphinx for documentation. To build the documentation you
will need sphinx installed, this can be done via pip.

A Makefile in the docs/ directory allows to build the documentation in
many formats. Among them, we usually consider html and latex.

Running Tests
-------------
Tests in pySMT are developed using python's built-in testing framework
unittest. Each TestCase is stored into a separate file, and is should
be possible to lunch it by calling the file directly, e.g.:

  ``python test_formula.py``

However, the preferred way is to use *nosetests*, e.g.:

  ``nosetests pysmt/tests/test_formula.py``

To launch all the tests, scripts *run_tests.sh* and *run_all_tests.sh* are
provided. We strive to keep the execution time of the tests
brief. *run_tests.sh* should complete within 1 minute. To achieve
this, we use parallel tests, and we skip slow tests. To run all tests,
use *run_all_tests.sh* this usually takes significantly longer (3 minutes).


Distributing PySMT
------------------

The setup.py script can be used to create distributable packages. The command

  `` python setup.py bdist --format=gztar ``

will produce a tar.gz file inside the ``dist/`` directory.

For convenience the script *make_distrib.sh* is provided, this builds
both the binary and source distributions within ``dist/``.
