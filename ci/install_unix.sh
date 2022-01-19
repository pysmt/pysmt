#!/bin/bash
set -ev

# This script directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Utility function to install packages in the OS
function os_install {
    PKG=${1}

    if [ ${AGENT_OS} == "Darwin" ];
    then
        # Convert package names from apt to brew naming
        case ${PKG} in
            "libmpc-dev")
                PKG="libmpc"
            ;;
            "libmpfr-dev")
                PKG="mpfr"
            ;;
            "libgmp-dev")
                PKG="gmp"
            ;;
        esac
        brew install "${PKG}" || (brew upgrade "${PKG}" && brew cleanup "${PKG}")
    else
        sudo apt install -y ${PKG}
    fi
}



# Use python or pypy as commands depending on the build
PYTHON="python"
if [ "${PYTHON_VERSION}" == "pypy" ] || [ "${PYTHON_VERSION}" == "pypy3" ]
then
    PYTHON="${PYTHON_VERSION}"
fi

# Fix problem with LIBDIR of Azure Pipelines
VRS=`python -c 'import platform;print(platform.python_version())'`
export PYSMT_PYTHON_LIBDIR="/opt/hostedtoolcache/Python/${VRS}/x64/lib/"

# 'pip install' command
PIP_INSTALL="${PYTHON} -m pip install --upgrade"

# Check that the correct version of Python is running.
${PYTHON} ${DIR}/check_python_version.py "${PYTHON_VERSION}"

# Install GMP for compiling mathsat bindings
if [ "${PYSMT_SOLVER}" == "msat" ] || [ "${PYSMT_SOLVER}" == "yices" ]
then
   os_install libgmp-dev
fi

# Install latest version of SWIG for CVC4 and BDD
# (The other solvers in isolation fall-back to the system swig)
if [ "${PYSMT_SOLVER}" == "cvc4" ] || [ "${PYSMT_SOLVER}" == "bdd" ] || [ "${PYSMT_SOLVER}" == "all" ]
then
    os_install flex
    os_install bison
    git clone https://github.com/swig/swig.git
    cd swig
    git checkout v4.0.2
    ./autogen.sh && ./configure && make
    sudo make install
    cd ..
fi
#
if [ "${PYSMT_SOLVER}" == "yices" ] || \
   [ "${PYSMT_SOLVER}" == "btor" ] || \
   [ "${PYSMT_SOLVER}" == "bdd" ] || \
   [ "${PYSMT_SOLVER}" == "picosat" ]
then
    os_install swig
fi

# GPerf is needed to compile Yices
if [ "${PYSMT_SOLVER}" == "yices" ] || [ "${PYSMT_SOLVER}" == "all" ]
then
    os_install gperf
fi

# Install dependencies
$PIP_INSTALL configparser
$PIP_INSTALL wheel
$PIP_INSTALL pytest

if [ "${PYSMT_SOLVER}" == "cvc4" ]
then
    $PIP_INSTALL toml
fi

# Install gmpy if needed
if [ "${PYSMT_GMPY}" == "TRUE" ]
then
    os_install libmpfr-dev
    os_install libmpc-dev
    $PIP_INSTALL gmpy2;
fi

# Install cython if needed
if [ "${PYSMT_CYTHON}" == "TRUE" ] || \
   [ "${PYSMT_SOLVER}" == "btor" ] || \
   [ "${PYSMT_SOLVER}" == "all" ]
then
    $PIP_INSTALL cython
fi

# Install the solver(s)!
${PYTHON} install.py --confirm-agreement

# Install the binaries for the *_wrap case
if [ "${PYSMT_SOLVER}" == "all" ] || [ "${PYSMT_SOLVER}" == *"z3_wrap"* ]; then
    ${PYTHON} install.py --z3 --conf --force;
    cp -v $(find ~/.smt_solvers/ -name z3 -type f) pysmt/test/smtlib/bin/z3;
    chmod +x pysmt/test/smtlib/bin/z3;
    mv pysmt/test/smtlib/bin/z3.solver.sh.template pysmt/test/smtlib/bin/z3.solver.sh ;
fi
if [ "${PYSMT_SOLVER}" == "all" ] || [ "${PYSMT_SOLVER}" == *"msat_wrap"* ];
then
    ${PYTHON} install.py --msat --conf --force;
    cp -v $(find ~/.smt_solvers/ -name mathsat -type f) pysmt/test/smtlib/bin/mathsat;
    mv pysmt/test/smtlib/bin/mathsat.solver.sh.template pysmt/test/smtlib/bin/mathsat.solver.sh ;
fi

# Check that the solvers are installed
${PYTHON} install.py --check
