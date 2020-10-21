#!/bin/bash
set -ev

# This script directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

#Python interpreter
PYTHON="python"

# 'pip install' command
PIP_INSTALL="${PYTHON} -m pip install --upgrade"

# Install dependencies
$PIP_INSTALL six
$PIP_INSTALL black

# Run check
${PYTHON} -m black --check ${DIR}/..
