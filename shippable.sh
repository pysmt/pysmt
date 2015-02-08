#!/bin/bash

if [ "$PYSMT_SOLVER" == "msat" ]
then

    pushd .
    cd solvers
    ./install.py --confirm-agreement --msat
    popd
fi

if [ "$PYSMT_SOLVER" == "z3" ]
then
    pushd .
    cd solvers
    ./install.py --confirm-agreement --z3 --make-j 2
    popd
fi

echo "Exiting..."
