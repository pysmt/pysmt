if [ "$1" == "msat" ]
then
    apt-get update
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --msat
fi

if [ "$1" == "z3" ]
then
    apt-get update
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --z3 --make-j 2
fi

if [ "$1" == "cvc4" ]
then
    apt-get update
    apt-get install -y make build-essential swig libgmp-dev \
                       python-all-dev \
                       autoconf libtool antlr3 wget \
                       curl libboost-dev
    ./install.py --confirm-agreement --cvc4
fi


if [ "$1" == "yices" ]
then
    easy_install ctypesgen
    ./install.py --confirm-agreement --yices
fi


if [ "$1" == "cudd" ]
then
    apt-get update
    apt-get install -y make build-essential swig
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --cudd  --make-j 2
fi

echo "Exiting..."
