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

    This should be used when applying a the function to the same
    formula is expected to yield different results, for example,
    serialization. If the operations are functions, consider using the
    DagWalker instead.

    The recursion within walk_ methods is obtained by using the
    'yield' keyword. In practice, each walk_ method is a generator
    that yields its arguments.
    If the generator returns None, no recursion will be performed.

    """

    def __init__(self, env=None):
        Walker.__init__(self, env)
        return

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

        iterator = f(formula)
        if iterator is None:
            return

        stack = [iterator]
        while stack:
            f = stack[-1]
            try:
                child = next(f)
                if threshold and len(stack) >= threshold:
                    iterator = self.walk_threshold(child)
                    if iterator is not None:
                        stack.append(iterator)
                else:
                    try:
                        cf = self.functions[child.node_type()]
                    except KeyError:
                        cf = self.walk_error
                    iterator = cf(child)
                    if iterator is not None:
                        stack.append(iterator)
            except StopIteration:
                stack.pop()
        return

    def walk_threshold(self, formula):
        raise NotImplementedError

    def walk_skip(self, formula):
        """ Default function to skip a node and process the children """
        for s in formula.args():
            yield s
        return


# EOC TreeWalker
