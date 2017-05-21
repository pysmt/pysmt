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
"""Provides walkers to navigate formulas.

Two types of walkers are provided: DagWalker and TreeWalker.

Internally, the Walkers have a dictionary that maps each FNode type to
the appropriate function to be called. When subclassing a Walker
remember to specify an action for the nodes of interest. Nodes for
which a behavior has not been specified will raise a
NotImplementedError exception.

Finally, an *experimental* meta class is provided called
CombinerWalker. This class takes a list of walkers and returns a new
walker that applies all the walkers to the formula. The idea is that
multiple information can be extracted from the formula by navigating
it only once.

"""

from pysmt.walkers.dag import DagWalker
assert DagWalker

from pysmt.walkers.tree import TreeWalker
assert TreeWalker

from pysmt.walkers.identitydag import IdentityDagWalker
assert IdentityDagWalker

from pysmt.walkers.generic import handles
assert handles
