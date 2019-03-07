#!/bin/bash
set -ev

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

PULL_REQUEST=${SYSTEM_PULLREQUEST_PULLREQUESTNUMBER}
BRANCH=${SYSTEM_PULLREQUEST_TARGETBRANCH}
OS=${AGENT_OS}

#
# Skip Install if Python 2.7 or PyPy and not a PR
#
if [ "${PULL_REQUEST}" == "false" ] && [ "${BRANCH}" != "master" ]; then
    echo "Regular Push (not PR) on non-master branch:"
    if [ "${PYTHON_VERSION}" == "2.7" ]; then
        echo "Skipping Python 2.7"
        exit 0
    fi
    if [ "${PYTHON_VERSION}" == "pypy" ]; then
        echo "Skipping Python PyPy"
        exit 0
    fi
    if [ "${PYSMT_SOLVER}" == "all" ]; then
        echo "Skipping 'all' configuration"
        exit 0
    fi
    if [ "${OS}" == "Darwin" ]; then
        echo "Skipping MacOSX build"
        exit 0
    fi
fi

function brew_install_or_upgrade {
    brew install "$1" || (brew upgrade "$1" && brew cleanup "$1")
}

if [ "${OS}" == "Darwin" ]; then
    brew update
    brew_install_or_upgrade openssl
    brew_install_or_upgrade readline
    brew_install_or_upgrade swig
    brew_install_or_upgrade gperf

    brew_install_or_upgrade mpfr
    brew_install_or_upgrade libmpc
    brew_install_or_upgrade gmp

    brew_install_or_upgrade pyenv
    brew_install_or_upgrade pyenv-virtualenv

    brew_install_or_upgrade readline
    brew_install_or_upgrade xz
    brew_install_or_upgrade zlib

    brew_install_or_upgrade libffi
    brew_install_or_upgrade ncurses

    pyenv install ${PYTHON_VERSION}

    pyenv virtualenv ${PYTHON_VERSION} venv

    eval "$(pyenv init -)"
    pyenv activate venv
fi

# Check that the correct version of Python is running.
python ${DIR}/check_python_version.py "${PYTHON_VERSION}"

# Install latest version of SWIG
if [ "${PYSMT_SOLVER}" == "bdd" ] || [ "${PYSMT_SOLVER}" == "cvc4" ] || [ "${PYSMT_SOLVER}" == "btor" ] || [ "${PYSMT_SOLVER}" == "all" ]
then
    git clone https://github.com/swig/swig.git
    cd swig
    git checkout rel-3.0.12
    ./autogen.sh && ./configure && make
    sudo make install
fi

if [ "${OS}" == "Darwin" ]; then
    eval "$(pyenv init -)"
    pyenv activate venv
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
    PYSMT_SOLVER_FOLDER="${PYSMT_SOLVER}_${OS_NAME}"
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
#  * Coverage is enabled only on master / all
if [ "${BRANCH}" == "master" ] && [ "${PYSMT_SOLVER}" == "all" ];
then
    python -m nose pysmt -v # --with-coverage --cover-package=pysmt
else
    python -m nose pysmt -v
fi

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
