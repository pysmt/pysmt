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

# Install the solvers
python install.py --confirm-agreement

python install.py --check
