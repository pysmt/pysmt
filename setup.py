from setuptools import setup, find_packages

import pysmt

long_description=\
"""============================================================
 pySMT: A library for SMT formulae manipulation and solving
============================================================

pySMT makes working with Satisfiability Modulo Theory simple.

Among others, you can:

* Define formulae in a solver independent way in a simple and
  inutitive way,
* Write ad-hoc simplifiers and operators,
* Dump your problems in the SMT-Lib format,
* Solve them using one of the native solvers, or by wrapping any
  SMT-Lib complaint solver.

Supported Theories and Solvers
==============================
pySMT provides methods to define a formula in Linear Real Arithmetic (LRA),
Real Difference Logic (RDL), their combination (LIRA),
Equalities and Uninterpreted Functions (EUF), Bit-Vectors (BV), and Arrays (A).
The following solvers are supported through native APIs:

* MathSAT (http://mathsat.fbk.eu/)
* Z3 (https://github.com/Z3Prover/z3/)
* CVC4 (http://cvc4.cs.nyu.edu/web/)
* Yices 2 (http://yices.csl.sri.com/)
* CUDD (http://vlsi.colorado.edu/~fabio/CUDD/)
* PicoSAT (http://fmv.jku.at/picosat/)
* Boolector (http://fmv.jku.at/boolector/)

Additionally, you can use any SMT-LIB 2 compliant solver.

PySMT assumes that the python bindings for the SMT Solver are installed and
accessible from your PYTHONPATH.


Wanna know more?
================

Visit http://www.pysmt.org
"""


setup(
    name='PySMT',
    version=pysmt.__version__,
    author='PySMT Team',
    author_email='info@pysmt.org',
    packages = find_packages(),
    include_package_data = True,
    url='http://www.pysmt.org',
    license='APACHE',
    description='A solver-agnostic library for SMT Formulae manipulation and solving',
    long_description=long_description,
    entry_points={
        'console_scripts': [
            'pysmt-install = pysmt.cmd.install:main',
        ],
    },
)
