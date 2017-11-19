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
from pysmt.walkers.tree import Walker


class DagWalker(Walker):
    """DagWalker treats the formula as a DAG and performs memoization of the
    intermediate results.

    This should be used when the result of applying the function to a
    formula is always the same, independently of where the formula has
    been found; examples include substitution and solving.

    Due to memoization, a few more things need to be taken into
    account when using the DagWalker.

    :func _get_key needs to be defined if additional arguments via
    keywords need to be shared. This function should return the key to
    be used in memoization. See substituter for an example.
    """

    def __init__(self, env=None, invalidate_memoization=False):
        """The flag ``invalidate_memoization`` can be used to clear the cache
        after the walk has been completed: the cache is one-time use.
        """
        Walker.__init__(self, env)

        self.memoization = {}
        self.invalidate_memoization = invalidate_memoization
        self.stack = []
        return

    def _get_children(self, formula):
        return formula.args()

    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""
        self.stack.append((True, formula))
        for s in self._get_children(formula):
            # Add only if not memoized already
            key = self._get_key(s, **kwargs)
            if key not in self.memoization:
                self.stack.append((False, s))

    def _compute_node_result(self, formula, **kwargs):
        """Apply function to the node and memoize the result.

        Note: This function assumes that the results for the children
              are already available.
        """
        key = self._get_key(formula, **kwargs)
        if key not in self.memoization:
            try:
                f = self.functions[formula.node_type()]
            except KeyError:
                f = self.walk_error

            args = [self.memoization[self._get_key(s, **kwargs)] \
                    for s in self._get_children(formula)]
            self.memoization[key] = f(formula, args=args, **kwargs)
        else:
            pass

    def _process_stack(self, **kwargs):
        """Empties the stack by processing every node in it.

        Processing is performed in two steps.
        1- A node is expanded and all its children are push to the stack
        2- Once all children have been processed, the result for the node
           is computed and memoized.
        """

        while self.stack:
            (was_expanded, formula) = self.stack.pop()
            if was_expanded:
                self._compute_node_result(formula, **kwargs)
            else:
                self._push_with_children_to_stack(formula, **kwargs)

    def iter_walk(self, formula, **kwargs):
        """Performs an iterative walk of the DAG"""
        self.stack.append((False, formula))
        self._process_stack(**kwargs)
        res_key = self._get_key(formula, **kwargs)
        return self.memoization[res_key]

    def walk(self, formula, **kwargs):
        if formula in self.memoization:
            return self.memoization[formula]

        res = self.iter_walk(formula, **kwargs)

        if self.invalidate_memoization:
            self.memoization.clear()
        return res

    def _get_key(self, formula, **kwargs):
        if not kwargs:
            return formula
        raise NotImplementedError("DagWalker should redefine '_get_key'" +
                                  " when using keywords arguments")

    def walk_true(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """ Returns True, independently from the children's value."""
        return True

    def walk_false(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """ Returns False, independently from the children's value."""
        return False

    def walk_none(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """ Returns None, independently from the children's value."""
        return None

    def walk_identity(self, formula, **kwargs):
        #pylint: disable=unused-argument
        """ Returns formula, independently from the childrens's value."""
        return formula

    def walk_any(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """ Returns True if any of the children returned True. """
        return any(args)

    def walk_all(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """ Returns True if all the children returned True. """
        return all(args)

# EOC DagWalker
