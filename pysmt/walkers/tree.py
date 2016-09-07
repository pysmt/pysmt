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
        return

    def _call_walk(self, function, formula):
        return function(formula)

    def walk(self, formula, threshold=None):
        """Generic walk method, will apply the function defined by the map
        self.functions.

        If threshold parameter is specified, the walk_threshold
        function will be called for all nodes with depth >= threshold.
        """

        try:
            f = self.functions[formula.node_type()]
        except KeyError:
            f = self.walk_error

        stack = [self._call_walk(f, formula)]
        while stack:
            f = stack[-1]
            try:
                child = next(f)
                if threshold and len(stack) >= threshold:
                    stack.append(self.walk_threshold(child))
                else:
                    try:
                        cf = self.functions[child.node_type()]
                    except KeyError:
                        cf = self.walk_error
                    stack.append(self._call_walk(cf, child))
            except StopIteration:
                stack.pop()
        return

    def walk_threshold(self, formula):
        raise NotImplementedError

    def walk_skip(self, formula):
        """ Default function to skip a node and process the children """
        for s in formula.args():
            yield (s)
        return


# EOC TreeWalker
