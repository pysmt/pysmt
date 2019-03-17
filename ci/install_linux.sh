#!/bin/bash
set -ev

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Check that the correct version of Python is running.
python ${DIR}/check_python_version.py "${PYTHON_VERSION}"

# Install latest version of SWIG for CVC4
# (The other solvers in isolation fall-back to the system swig)
if [ "${PYSMT_SOLVER}" == "cvc4" ] || [ "${PYSMT_SOLVER}" == "all" ]
then
    sudo apt install -y flex bison
    git clone https://github.com/swig/swig.git
    cd swig
    git checkout rel-3.0.12
    ./autogen.sh && ./configure && make
    sudo make install
    cd ..
fi
#
if [ "${PYSMT_SOLVER}" == "yices" ] || [ "${PYSMT_SOLVER}" == "btor" ] || [ "${PYSMT_SOLVER}" == "bdd" ] || [ "${PYSMT_SOLVER}" == "picosat" ]
then
    sudo apt install -y swig
fi

echo "Check that the correct version of Python is running"
python ${DIR}/check_python_version.py "${PYTHON_VERSION}"

PIP_INSTALL="python -m pip install --upgrade"

$PIP_INSTALL configparser
$PIP_INSTALL six
$PIP_INSTALL cython
$PIP_INSTALL wheel
$PIP_INSTALL nose

if [ "${PYSMT_SOLVER}" == "all" ] || [ "${PYSMT_SOLVER}" == *"btor"* ];
then
    $PIP_INSTALL python-coveralls;
fi

if [ "${PYSMT_GMPY}" == "TRUE" ];
then
    $PIP_INSTALL gmpy2;
fi


if [ "${PYSMT_CUSTOM_BINDINGS_PATH}" == "TRUE" ]; then
    PYSMT_SOLVER_FOLDER="${PYSMT_SOLVER}_${AGENT_OS}"
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






################################################################################
# Run!

echo "${PYTHONPATH}"
python install.py --env
python install.py --check

#
# Run the test suite
python -m nose pysmt -v # --with-coverage --cover-package=pysmt

#
# Test examples in examples/ folder
#
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
