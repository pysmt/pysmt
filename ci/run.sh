#!/bin/bash

set -ev

PYTHON="python"
if [ "${PYTHON_VERSION}" == "pypy" ] || [ "${PYTHON_VERSION}" == "pypy3" ]
then
    PYTHON="${PYTHON_VERSION}"
fi

# Check that the solvers are installed
${PYTHON} -m pysmt install --check

# Run the test suite
${PYTHON} -m pytest tests -v # --with-coverage --cover-package=pysmt


# Test examples in examples/ folder
if [ "${PYSMT_SOLVER}" == "all" ];
then
    ${PYTHON} -m pysmt install --msat --conf --force;
    cp -v $(find ~/.smt_solvers/ -name mathsat -type f) /tmp/mathsat;

    for ex in examples/*.py; do
        echo $ex
        ${PYTHON} $ex
    done

    # xoxo reads the moves from stdin, so play a scripted game instead and
    # check that it gets as far as announcing a result
    echo examples/xoxo/xoxo.py
    xoxo_log=$(${PYTHON} examples/xoxo/xoxo.py --moves 1,2,3,4,5,6,7,8,9)
    echo "${xoxo_log}"
    grep -qE "wins|draw" <<< "${xoxo_log}"
fi
