apt-get update

if [ "$1" == "msat" ] || [ "$1" == "all" ]
then
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --msat
fi

if [ "$1" == "msat_wrap" ] || [ "$1" == "all" ]
then
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --msat
fi


if [ "$1" == "z3" ] || [ "$1" == "all" ]
then
    apt-get install -y make build-essential swig libgmp-dev
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --z3 --make-j 2
fi

if [ "$1" == "cvc4" ] || [ "$1" == "all" ]
then
    apt-get install -y make build-essential swig libgmp-dev \
                       python-all-dev \
                       autoconf libtool antlr3 wget \
                       curl libboost-dev
    ./install.py --confirm-agreement --cvc4
fi


if [ "$1" == "yices" ] || [ "$1" == "all" ]
then
    easy_install ctypesgen
    ./install.py --confirm-agreement --yices
fi


if [ "$1" == "cudd" ] || [ "$1" == "all" ]
then
    apt-get install -y make build-essential swig
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --cudd  --make-j 2
fi


if [ "$1" == "picosat" ] || [ "$1" == "all" ]
then
    apt-get install -y make build-essential swig
    apt-get install -y python-all-dev
    ./install.py --confirm-agreement --picosat
fi

echo "All done for '$1'..."
echo "Exiting..."
