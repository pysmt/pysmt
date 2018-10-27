#!/bin/bash
set -ev

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

#
# Skip Install if Python 2.7 or PyPy and not a PR
#
if [ "${TRAVIS_PULL_REQUEST}" == "false" ] && [ "${TRAVIS_BRANCH}" != "master" ]; then
    echo "Regular Push (not PR) on non-master branch:"
    if [ "${TRAVIS_PYTHON_VERSION}" == "2.7" ]; then
        echo "Skipping Python 2.7"
        exit 0
    fi
    if [ "${TRAVIS_PYTHON_VERSION}" == "pypy" ]; then
        echo "Skipping Python PyPy"
        exit 0
    fi
    if [ "${PYSMT_SOLVER}" == "all" ]; then
        echo "Skipping 'all' configuration"
        exit 0
    fi
    if [ "${TRAVIS_OS_NAME}" == "osx" ]; then
        echo "Skipping MacOSX build"
        exit 0
    fi
fi

if [ "${TRAVIS_OS_NAME}" == "osx" ]; then
    eval "$(pyenv init -)"
    pyenv activate venv
fi
echo "Check that the correct version of Python is running"
python ${DIR}/check_python_version.py "${TRAVIS_PYTHON_VERSION}"

PIP_INSTALL="python -m pip install --upgrade"

$PIP_INSTALL configparser
$PIP_INSTALL six
$PIP_INSTALL cython
$PIP_INSTALL wheel

if [ "${PYSMT_SOLVER}" == "all" ] || [ "${PYSMT_SOLVER}" == *"btor"* ];
then
    $PIP_INSTALL python-coveralls;
fi

if [ "${PYSMT_GMPY}" == "TRUE" ];
then
    $PIP_INSTALL gmpy2;
fi

# Adding Python 3.7 library path to GCC search
if [ "${TRAVIS_PYTHON_VERSION}" == "3.7" ]; then
    export LIBRARY_PATH="/opt/python/3.7.1/lib:${LIBRARY_PATH}"
    export CPATH="/opt/python/3.7.1/include/python3.7m:${CPATH}"
fi


#
# Install Solvers
#
if [ "${PYSMT_CUSTOM_BINDINGS_PATH}" == "TRUE" ]; then
    PYSMT_SOLVER_FOLDER="${PYSMT_SOLVER}_${TRAVIS_OS_NAME}"
    PYSMT_SOLVER_FOLDER="${PYSMT_SOLVER_FOLDER//,/$'_'}"
    BINDINGS_FOLDER="${HOME}/python_bindings/${PYSMT_SOLVER_FOLDER}"
    python install.py --confirm-agreement --bindings-path "${BINDINGS_FOLDER}"
    eval "$(python install.py --env --bindings-path "${BINDINGS_FOLDER}")"
else
    python install.py --confirm-agreement
fi

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


# On OSX install nosetest
if [ "${TRAVIS_OS_NAME}" == "osx" ]; then
    $PIP_INSTALL nose
fi
