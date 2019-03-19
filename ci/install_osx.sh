#!/bin/bash
set -ev

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PIP_INSTALL="python -m pip install --upgrade"

# Utility function to install packages
function brew_install_or_upgrade {
    brew install "$1" || (brew upgrade "$1" && brew cleanup "$1")
}


# Check that the correct version of Python is running.
python ${DIR}/check_python_version.py "${PYTHON_VERSION}"

# Install GMP for compiling mathsat bindings
if [ "${PYSMT_SOLVER}" == "msat" ] || [ "${PYSMT_SOLVER}" == "yices" ]
then
   brew_install_or_upgrade gmp
fi

# Install latest version of SWIG for CVC4
# (The other solvers in isolation fall-back to the system swig)
if [ "${PYSMT_SOLVER}" == "yices" ] || \
   [ "${PYSMT_SOLVER}" == "btor" ] || \
   [ "${PYSMT_SOLVER}" == "bdd" ] || \
   [ "${PYSMT_SOLVER}" == "picosat" ] || \
   [ "${PYSMT_SOLVER}" == "cvc4" ] || \
   [ "${PYSMT_SOLVER}" == "all" ]
then
    brew_install_or_upgrade swig
fi

# Install dependencies
$PIP_INSTALL configparser
$PIP_INSTALL six
$PIP_INSTALL wheel
$PIP_INSTALL nose

# Install gmpy if needed
if [ "${PYSMT_CYTHON}" == "TRUE" ] || \
   [ "${PYSMT_SOLVER}" == "btor" ] || \
   [ "${PYSMT_SOLVER}" == "all" ]
then
    brew_install_or_upgrade mpfr libmpc
    $PIP_INSTALL gmpy2;
fi

# Install cython if needed
if [ "${PYSMT_CYTHON}" == "TRUE" ] || [ "${PYSMT_SOLVER}" == "btor" ]
then
    $PIP_INSTALL cython
fi


# Install the solver(s)!
python install.py --confirm-agreement

# Install the binaries for the *_wrap case
if [ "${PYSMT_SOLVER}" == "all" ] || [ "${PYSMT_SOLVER}" == *"z3_wrap"* ]; then
    python install.py --z3 --conf --force;
    cp -v $(find ~/.smt_solvers/ -name z3 -type f) pysmt/test/smtlib/bin/z3;
    chmod +x pysmt/test/smtlib/bin/z3;
    mv pysmt/test/smtlib/bin/z3.solver.sh.template pysmt/test/smtlib/bin/z3.solver.sh ;
fi
if [ "${PYSMT_SOLVER}" == "all" ] || [ "${PYSMT_SOLVER}" == *"msat_wrap"* ];
then
    python install.py --msat --conf --force;
    cp -v $(find ~/.smt_solvers/ -name mathsat -type f) pysmt/test/smtlib/bin/mathsat;
    mv pysmt/test/smtlib/bin/mathsat.solver.sh.template pysmt/test/smtlib/bin/mathsat.solver.sh ;
fi

# Check that the solvers are installed
python install.py --check


# Run the test suite
python -m nose pysmt -v # --with-coverage --cover-package=pysmt


# Test examples in examples/ folder
if [ "${PYSMT_SOLVER}" == "all" ];
then
    python install.py --msat --conf --force;
    cp -v $(find ~/.smt_solvers/ -name mathsat -type f) /tmp/mathsat;

    # since we're relying on relative `pysmt` import in examples,
    # ensure `.` is added to `sys.path`
    export PYTHONPATH=${PYTHONPATH:-.}

    for ex in examples/*.py; do
        echo $ex
        python $ex
    done
fi
