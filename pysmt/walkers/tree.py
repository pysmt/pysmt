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
from pysmt.walkers.generic import Walker

class TreeWalker(Walker):
    """TreeWalker treats the formula as a Tree and does not perform memoization.

    This should be used when applying a the function to the same formula is
    expected to yield different results, for example, serialization.
    """

    def __init__(self, env=None):
        Walker.__init__(self, env)
        self.threshold_cnt = -1
        return


    def walk(self, formula):
        """ Generic walk method, will apply the function defined by the map
        self.functions.
        """
        if self.threshold_cnt == 0:
            self.walk_threshold(formula)
            return
        if self.threshold_cnt >= 0: self.threshold_cnt -= 1

        try:
            f = self.functions[formula.node_type()]
        except KeyError:
            f = self.walk_error

        f(formula) # Apply the function to the formula

        if self.threshold_cnt >= 0: self.threshold_cnt += 1
        return

    def walk_threshold(self, formula):
        raise NotImplementedError

    def walk_skip(self, formula):
        """ Default function to skip a node and process the children """
        for s in formula.args():
            self.walk(s)
        return


# EOC TreeWalker
