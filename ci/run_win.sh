#!/bin/bash
set -ev

python install.py --check
python -m nose -v
