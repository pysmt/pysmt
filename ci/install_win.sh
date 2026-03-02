#!/bin/bash
set -ev

if [ "${PYTHON_VERSION}" == "2.7" ]
then
    choco install vcpython27
fi

python --version
python -c "import struct; print(struct.calcsize('P') * 8)"
python -m pip install -r dev-requirements.txt
python -m pip install --upgrade setuptools

if [ "${PYSMT_SOLVER}" == "msat" ] || [ "${PYSMT_SOLVER}" == "all" ]
then
    # VCPKG_INSTALLATION_ROOT is a default env var on GH runners
    VCPKG_ROOT="$VCPKG_INSTALLATION_ROOT/installed/x64-windows"

    # Tell the compiler and linker where to look
    INCLUDE="$VCPKG_ROOT/include;$INCLUDE"
    LIB="$VCPKG_ROOT/lib;$LIB"
    PATH="$VCPKG_ROOT/bin;$PATH" # For DLLs at runtime
fi

# Install the solvers
python install.py --confirm-agreement

python install.py --check
