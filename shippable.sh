#!/bin/bash

# Remove all solvers and pysmt itself from PYTHONPATH
export PYTHONPATH=""

if [ "$1" == "all" ]
then
    if [ "$2" == "3.4" ]
    then
        export PYTHONPATH="${PYSMT_MSAT_PATH_3}:${PYSMT_PICOSAT_PATH_3}:${PYSMT_BTOR_PATH_3}"
    else
        export PYTHONPATH="${PYSMT_MSAT_PATH}:${PYSMT_Z3_PATH}:${PYSMT_CVC4_PATH}:${PYSMT_YICES_PATH}:${PYSMT_PYCUDD_PATH}:${PYSMT_PICOSAT_PATH}:${PYSMT_BTOR_PATH}"
    fi
fi


if [ "$1" == "msat" ]
then
    if [ "$2" == "3.4" ]
    then
        export PYTHONPATH="${PYSMT_MSAT_PATH_3}"
    else
        export PYTHONPATH="${PYSMT_MSAT_PATH}"
    fi
fi


if [ "$1" == "z3" ]
then
    export PYTHONPATH="${PYSMT_Z3_PATH}"
fi


if [ "$1" == "cvc4" ]
then
    export PYTHONPATH="${PYSMT_CVC4_PATH}"
fi


if [ "$1" == "yices" ]
then
    export PYTHONPATH="${PYSMT_YICES_PATH}"
fi


if [ "$1" == "cudd" ]
then
    export PYTHONPATH="${PYSMT_PYCUDD_PATH}"
fi


if [ "$1" == "picosat" ]
then
    if [ "$2" == "3.4" ]
    then
        export PYTHONPATH="${PYSMT_PICOSAT_PATH_3}"
    else
        export PYTHONPATH="${PYSMT_PICOSAT_PATH}"
    fi

fi

if [ "$1" == "btor" ]
then
    if [ "$2" == "3.4" ]
    then
        export PYTHONPATH="${PYSMT_BTOR_PATH_3}"
    else
        export PYTHONPATH="${PYSMT_BTOR_PATH}"
    fi

fi

echo "All done for '$1'..."
echo "Exiting..."
