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
from pysmt.walkers import DagWalker


class PolarityDagWalker(DagWalker):
    """A DagWalker that keeps track of the polarity of the formula.

    Many rewriting techniques need to know the polarity of a formula
    (i.e., whether it occurs under an even or odd number of negations).
    """
    def __init__(self, env=None, invalidate_memoization=False):
        DagWalker.__init__(self, env=env,
                           invalidate_memoization=invalidate_memoization)

    def iter_walk(self, formula, **kwargs):
        """Performs an iterative walk of the DAG"""
        self.stack.append((False, formula, True))
        self._process_stack(**kwargs)
        res_key = self._get_key(formula, True, **kwargs)
        return self.memoization[res_key]

    def _push_with_children_to_stack(self, formula, polarity, **kwargs):
        """Add children to the stack."""
        self.stack.append((True, formula, True))
        if formula.is_not():
            new_polarity = not polarity
        elif formula.is_implies():
            left, right = formula.get_sons()
            # Left has opposite polarity
            key = self._get_key(left, not polarity, **kwargs)
            if key not in self.memoization:
                self.stack.append((False, left, not polarity))
            # Right has the same polarity
            key = self._get_key(right, polarity, **kwargs)
            if key not in self.memoization:
                self.stack.append((False, right, polarity))
            return
        else:
            assert not formula.is_iff(), "Operator IFF not supported"
            new_polarity = polarity

        for s in formula.get_sons():
            # Add only if not memoized already
            key = self._get_key(s, new_polarity, **kwargs)
            if key not in self.memoization:
                self.stack.append((False, s, new_polarity))

    def _compute_node_result(self, formula, polarity, **kwargs):
        """Apply function to the node and memoize the result.

        Note: This function assumes that the results for the children
              are already available.
        """
        key = self._get_key(formula, polarity, **kwargs)
        if key not in self.memoization:
            try:
                f = self.functions[formula.node_type()]
            except KeyError:
                f = self.walk_error

            args = [self.memoization[self._get_key(s, polarity, **kwargs)] \
                    for s in formula.get_sons()]
            self.memoization[key] = f(formula, polarity, args=args, **kwargs)
        else:
            pass

    def _process_stack(self, **kwargs):
        """Empties the stack by processing every node in it.

        Processing is performed in two steps.
        1- A node is expanded and all its children are push to the stack
        2- Once all children have been processed, the result for the node
           is computed and memoized.
        """

        while len(self.stack) > 0 :
            (was_expanded, formula, pos_polarity) = self.stack.pop()
            if was_expanded:
                self._compute_node_result(formula, pos_polarity, **kwargs)
            else:
                self._push_with_children_to_stack(formula, pos_polarity, **kwargs)

    def _get_key(self, formula, polarity, **kwargs):
        if len(kwargs) == 0:
            return (formula, polarity)
        raise NotImplementedError("DagWalker should redefine '_get_key'" +
                                  " when using keywords arguments")

    def walk_identity(self, formula, polarity, args):
        return formula
