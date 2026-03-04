#!/bin/bash

set -ev

PYTHON="python"
if [ "${PYTHON_VERSION}" == "pypy" ] || [ "${PYTHON_VERSION}" == "pypy3" ]
then
    PYTHON="${PYTHON_VERSION}"
fi

# Check that the solvers are installed
${PYTHON} install.py --check

# Run the test suite
${PYTHON} -m pytest pysmt -v # --with-coverage --cover-package=pysmt


# Test examples in examples/ folder
if [ "${PYSMT_SOLVER}" == "all" ];
then
    ${PYTHON} install.py --msat --conf --force;
    cp -v $(find ~/.smt_solvers/ -name mathsat -type f) /tmp/mathsat;

    # since we're relying on relative `pysmt` import in examples,
    # ensure `.` is added to `sys.path`
    export PYTHONPATH=${PYTHONPATH:-.}

    for ex in examples/*.py; do
        echo $ex
        ${PYTHON} $ex
    done
fi
