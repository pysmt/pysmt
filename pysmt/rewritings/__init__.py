#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
"""This module defines multiple rewritings for pySMT expressions.

Each file in this module contains one particular rewriter. High-level
methods are collected here for convenience.

"""
# pylint: disable=unused-import

from pysmt.rewritings.cnf import cnf, cnf_as_set
from pysmt.rewritings.nnf import nnf
from pysmt.rewritings.prenex import prenex_normal_form
from pysmt.rewritings.aig import aig
from pysmt.rewritings.partition import conjunctive_partition
from pysmt.rewritings.partition import disjunctive_partition
