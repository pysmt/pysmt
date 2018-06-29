#!/bin/bash
set -ev

#
# Skip Install if Python 2.7 or PyPy and not a PR
#
if [ "${TRAVIS_PULL_REQUEST}" == "false" ] && [ "${TRAVIS_BRANCH}" != "master" ]; then
    echo "Regular Push (not PR) on non-master branch:"
    if [ "${TRAVIS_PYTHON_VERSION}" == "2.7" ]; then
        echo "Skipping Python 2.7"
        exit 0
    fi
    if [ "${TRAVIS_PYTHON_VERSION}" == "pypy" ]; then
        echo "Skipping Python PyPy"
        exit 0
    fi
    if [ "${PYSMT_SOLVER}" == "all" ]; then
        echo "Skipping 'all' configuration"
        exit 0
    fi
    if [ "${TRAVIS_OS_NAME}" == "osx" ]; then
        echo "Skipping MacOSX build"
        exit 0
    fi
fi

function brew_install_or_upgrade {
    brew install "$1" || (brew upgrade "$1" && brew cleanup "$1")
}

if [ "${TRAVIS_OS_NAME}" == "osx" ]; then
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


    pyenv install ${TRAVIS_PYTHON_VERSION}

    pyenv virtualenv ${TRAVIS_PYTHON_VERSION} venv

    # Check that the correct version of Python is running.
    python --version
fi
