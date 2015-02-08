#!/bin/bash

if [ "$PYSMT_SOLVER" == "msat" ]
then
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev
    pushd .
    cd solvers
    ./install.py --confirm-agreement --msat
    popd
    echo "MSAT Installed"
fi

if [ "$PYSMT_SOLVER" == "z3" ]
then
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev

    pushd .
    cd solvers
    ./install.py --confirm-agreement --z3 --make-j 2
    popd
fi

echo "Exiting..."
