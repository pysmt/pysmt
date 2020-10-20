#!/bin/bash

export PYTHONDONTWRITEBYTECODE=True
python3 -mpytest -m "not slow"
