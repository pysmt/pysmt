#!/bin/bash
set -ev

# This script directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Windows has its own way
if [[ "${AGENT_OS}" == *"windows"* ]];
then
    . ${DIR}/install_win.sh
    exit $?
else
    . ${DIR}/install_unix.sh
    exit $?
fi
