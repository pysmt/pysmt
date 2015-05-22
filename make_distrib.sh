#!/bin/bash

python setup.py bdist --format=gztar
python setup.py sdist --format=gztar

# Wheel file
python setup.py bdist_wheel --universal

wget https://bitbucket.org/gutworth/six/raw/8a545f4e906f6f479a6eb8837f31d03731597687/six.py -O dist/six.py
echo "To create a self-contained wheel pkg, manually add six:"
echo " $ zip PySMT-version.whl six.py"
echo "A copy of six.py has been downloaded in dist/"
