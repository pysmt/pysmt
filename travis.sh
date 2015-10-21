#!/bin/bash

export Z3_PYTHONPATH="${TRAVIS_BUILD_DIR}/.smt_solvers/z3_bin/lib/python${TRAVIS_PYTHON_VERSION}/dist-packages"
export CVC4_PYTHONPATH="${TRAVIS_BUILD_DIR}/.smt_solvers/CVC4_bin/share/pyshared:${TRAVIS_BUILD_DIR}/.smt_solvers/CVC4_bin/lib/pyshared"
export PICOSAT_PYTHONPATH="${TRAVIS_BUILD_DIR}/.smt_solvers/picosat-960:${TRAVIS_BUILD_DIR}/.smt_solvers/picosat-960/build/lib.linux-x86_64-${TRAVIS_PYTHON_VERSION}"
export CUDD_PYTHONPATH="${TRAVIS_BUILD_DIR}/.smt_solvers/repycudd-4861f4df8abc2ca205a6a09b30fdc8cfd29f6ebb"
export BTOR_PYTHONPATH="${TRAVIS_BUILD_DIR}/.smt_solvers/boolector-2.1.1-with-lingeling-b85/boolector"
export YICES_PYTHONPATH="${TRAVIS_BUILD_DIR}/.smt_solvers/pyices-aa0b91c39aa00c19c2160e83aad822dc468ce328/build/lib.linux-x86_64-${TRAVIS_PYTHON_VERSION}:${HOME}/.local/lib/python${TRAVIS_PYTHON_VERSION}/site-packages"
export MSAT_PYTHONPATH="${TRAVIS_BUILD_DIR}/.smt_solvers/mathsat-5.3.8-linux-x86_64/python:${TRAVIS_BUILD_DIR}/.smt_solvers/mathsat-5.3.8-linux-x86_64/python/build/lib.linux-x86_64-${TRAVIS_PYTHON_VERSION}"


if [ "${PYSMT_SOLVER}" == "all" ]
then
    for solver in msat z3 cvc4 yices cudd picosat btor
    do
        export PYSMT_SOLVER="$solver"
        source ./travis.sh
    done
    export PYSMT_SOLVER="all"

else

    if [ "${PYSMT_SOLVER}" == "msat" ]
    then
        export PYTHONPATH="${PYTHONPATH}:${MSAT_PYTHONPATH}"
    fi

    if [ "${PYSMT_SOLVER}" == "z3" ]
    then
        export PYTHONPATH="${PYTHONPATH}:${Z3_PYTHONPATH}"
    fi

    if [ "${PYSMT_SOLVER}" == "cvc4" ]
    then
        export PYTHONPATH="${PYTHONPATH}:${CVC4_PYTHONPATH}"
    fi


    if [ "${PYSMT_SOLVER}" == "yices" ]
    then
        export PYTHONPATH="${PYTHONPATH}:${YICES_PYTHONPATH}"
    fi


    if [ "${PYSMT_SOLVER}" == "cudd" ]
    then
        export PYTHONPATH="${PYTHONPATH}:${CUDD_PYTHONPATH}"
    fi


    if [ "${PYSMT_SOLVER}" == "picosat" ]
    then
        export PYTHONPATH="${PYTHONPATH}:${PICOSAT_PYTHONPATH}"
    fi

    if [ "${PYSMT_SOLVER}" == "btor" ]
    then
        export PYTHONPATH="${PYTHONPATH}:${BTOR_PYTHONPATH}"
    fi

    python ./install.py --check

    if [ "$?" != 0 ]
    then
        if [ "${PYSMT_SOLVER}" == "msat" ]
        then
            python ./install.py --confirm-agreement --msat
        fi

        if [ "${PYSMT_SOLVER}" == "z3" ]
        then
            python ./install.py --confirm-agreement --z3 --make-j 2
        fi

        if [ "${PYSMT_SOLVER}" == "cvc4" ]
        then
            python ./install.py --confirm-agreement --cvc4
        fi


        if [ "${PYSMT_SOLVER}" == "yices" ]
        then
            pip install ctypesgen
            python ./install.py --confirm-agreement --yices
        fi


        if [ "${PYSMT_SOLVER}" == "cudd" ]
        then
            python ./install.py --confirm-agreement --cudd  --make-j 2
        fi


        if [ "${PYSMT_SOLVER}" == "picosat" ]
        then
            python ./install.py --confirm-agreement --picosat
        fi

        if [ "${PYSMT_SOLVER}" == "btor" ]
        then
            LIBFILE=`find / -name "libpython3.4m.so" | head -n 1`
            LIBDIR=`dirname ${LIBFILE}`
            echo "Found libpython3.4m.so in ${LIBFILE} in path ${LIBDIR}"
            export LIBRARY_PATH="$LIBRARY_PATH:${LIBDIR}"
            pip install cython
            python ./install.py --confirm-agreement --btor
        fi
    fi
fi

if [ "${PYSMT_SOLVER}" == "msat_wrap" ] || [ "${PYSMT_SOLVER}" == "all" ]
then
    if [ ! -f .smt_solvers/mathsat-5.3.8-linux-x86_64/bin/mathsat ]
    then
        python ./install.py --confirm-agreement --msat
    fi
    cp .smt_solvers/mathsat-5.3.8-linux-x86_64/bin/mathsat ${TRAVIS_BUILD_DIR}/pysmt/test/smtlib/bin
    mv ${TRAVIS_BUILD_DIR}/pysmt/test/smtlib/bin/mathsat.solver.sh.template ${TRAVIS_BUILD_DIR}/pysmt/test/smtlib/bin/mathsat.solver.sh
fi

if [ "${PYSMT_SOLVER}" == "z3_wrap" ] || [ "${PYSMT_SOLVER}" == "all" ]
then
    if [ ! -f .smt_solvers/z3_bin/bin/z3 ]
    then
        python ./install.py --confirm-agreement --z3
    fi
    cp .smt_solvers/z3_bin/bin/z3 ${TRAVIS_BUILD_DIR}/pysmt/test/smtlib/bin
    mv ${TRAVIS_BUILD_DIR}/pysmt/test/smtlib/bin/z3.solver.sh.template ${TRAVIS_BUILD_DIR}/pysmt/test/smtlib/bin/z3.solver.sh
fi


echo "All done for '${PYSMT_SOLVER}'..."
echo "Exiting..."
