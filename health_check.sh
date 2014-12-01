#!/bin/bash

export PYTHONDONTWRITEBYTECODE=True
nosetests -A "not slow" \
          --with-xunit \
          --with-coverage --cover-html --cover-package=pysmt
