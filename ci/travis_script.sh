#!/bin/bash
set -ev

#
# Skip Install if Python 2.7 or PyPy and not a PR
#
if [ "${TRAVIS_PULL_REQUEST}" == "false" ]; then
    echo "Regular Push (Not-PR):"
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
fi

export BINDINGS_FOLDER=${HOME}/python_bindings/${PYSMT_SOLVER}
eval `python install.py --env --bindings-path ${BINDINGS_FOLDER}`
echo ${PYTHONPATH}

#
# Run the test suite
#
nosetests pysmt -v

#
# Test examples in examples/ folder
#
if [ "${PYSMT_SOLVER}" == "all" ];
then
    python install.py --msat --conf --force;
    cp -v $(find ~/.smt_solvers/ -name mathsat -type f) /tmp/mathsat;
    (for ex in `ls examples/*.py`; do echo $ex; python $ex || exit $?; done);
fi
