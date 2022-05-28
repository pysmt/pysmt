#!/bin/bash

# Replace version information
# See: https://git-scm.com/docs/git-describe
# E.g. v0.5.1-4-g49a49f2-wip
#      * 4 commits after tag v0.5.1
#      * Latest commit "49a49f2"
# we get v0.5.1.dev4
#
DEV_VERSION=`git describe | sed  's/v\(.*\)-\(.*\)-\(.*\)/\2/'`
sed -i "s/\"dev\", 1/\"dev\", $DEV_VERSION/" pysmt/__init__.py

# Create package files
python3 setup.py sdist --format=gztar

# Wheel file
python3 setup.py bdist_wheel --universal