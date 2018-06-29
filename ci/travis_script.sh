#!/bin/bash
set -ev


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

PYSMT_SOLVER_FOLDER="${PYSMT_SOLVER}_${TRAVIS_OS_NAME}"
PYSMT_SOLVER_FOLDER="${PYSMT_SOLVER_FOLDER//,/$'_'}"
export BINDINGS_FOLDER=${HOME}/python_bindings/${PYSMT_SOLVER_FOLDER}

eval `python install.py --env --bindings-path ${BINDINGS_FOLDER}`
echo ${PYTHONPATH}
python install.py --check

#
# Run the test suite
#  * Coverage is enabled only on master / all
if [ "${TRAVIS_BRANCH}" == "master" ] && [ "${PYSMT_SOLVER}" == "all" ];
then
    python -m nose pysmt -v # --with-coverage --cover-package=pysmt
else
    python -m nose pysmt -v
fi

#
# Test examples in examples/ folder
#
if [ "${PYSMT_SOLVER}" == "all" ];
then
    python install.py --msat --conf --force;
    cp -v $(find ~/.smt_solvers/ -name mathsat -type f) /tmp/mathsat;
    (for ex in `ls examples/*.py`; do echo $ex; python $ex || exit $?; done);
fi
