#!/bin/bash

if [ "$1" == "msat" ]
then
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev
    pushd .
    cd solvers
    ./install.py --confirm-agreement --msat
    popd
    echo "MSAT Installed"
fi

if [ "$1" == "z3" ]
then
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev

    pushd .
    cd solvers
    ./install.py --confirm-agreement --z3 --make-j 2
    popd
fi

echo "Exiting..."
