.. PySMT documentation master file, created by
   sphinx-quickstart on Sun Feb 16 16:14:52 2014.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Welcome to pySMT's documentation!
=================================

=============
 Introduction
=============

pySMT makes working with `Satisfiability Modulo Theory`_ simple.
pySMT provides an intermediate step between the `SMT-LIB`_ (that is
universal but not programmable) and solvers API (that are programmable,
but specific).

.. _Satisfiability Modulo Theory: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
.. _SMT-LIB: http://smt-lib.org

Among others, you can:

* Define formulae in a solver independent way
* Run the same code using multiple solvers
* Easily perform quantifier elimination, interpolation and unsat-core extraction
* Write ad-hoc simplifiers and operators
* and more...

Please let us know of any problem or possible improvements by opening
an issue on `github`_ or by writing to pysmt@googlegroups.com .

.. _github: https://github.com/pysmt/pysmt/issues

Where to go from here:

* Getting Started: :ref:`Installation <getting-started>` and :ref:`Hello
  World <gs-hello-world>`;


* :doc:`Tutorials <tutorials>`: Simple examples showing how to perform common operations using pySMT.

* Full :ref:`API Reference <api-ref>`

* :ref:`Extending pySMT <development>`


Table of Contents
=================

.. toctree::
   :maxdepth: 2

   getting_started
   tutorials
   CHANGES
   development
   api_ref


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
