#!/bin/bash
set -ev

python --version
python -c "import struct; print(struct.calcsize('P') * 8)"
python -m pip install -e . pytest
python -m pip install --upgrade setuptools

# Install the solvers
python -m pysmt install --confirm-agreement

python -m pysmt install --check
