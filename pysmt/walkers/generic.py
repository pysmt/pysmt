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
from functools import partial

import sys
if sys.version_info >= (3, 3):
    from collections.abc import Iterable
else:
    from collections import Iterable

import pysmt.operators as op
import pysmt.exceptions

# NodeType to Function Name
def nt_to_fun(o):
    """Returns the name of the walk function for the given nodetype."""
    return "walk_%s" % op.op_to_str(o).lower()

class handles(object):
    """Decorator for walker functions.

    Use it by specifying the nodetypes that need to be handled by the
    given function. It is possible to use groupd (e.g., op.RELATIONS)
    directly. ::

      @handles(op.NODE, ...)
      def walk_special(...):
         ...

    """
    def __init__(self, *nodetypes):
        if len(nodetypes) == 1 and isinstance(nodetypes[0], Iterable):
            nodetypes = nodetypes[0]
        self.nodetypes = list(nodetypes)

    def __call__(self, func):
        nodetypes = self.nodetypes
        if hasattr(func, "nodetypes"):
            nodetypes = func.nodetypes + nodetypes
        func.nodetypes = nodetypes
        return func

class MetaNodeTypeHandler(type):
    """Metaclass used to intepret the nodehandler decorator. """
    def __new__(cls, name, bases, dct):
        obj = type.__new__(cls, name, bases, dct)
        for k,v in dct.items():
            if hasattr(v, "nodetypes"):
                obj.set_handler(v, *v.nodetypes)
        return obj


class Walker(object, metaclass=MetaNodeTypeHandler):
    """Base Abstract Walker class.

    Do not subclass directly, use DagWalker or TreeWalker, instead.
    """

    def __init__(self, env=None):
        if env is None:
            import pysmt.environment
            env = pysmt.environment.get_env()
        self.env = env

        self.functions = {}
        for o in op.all_types():
            try:
                # getattr will raise an AttributeError exception if a
                # method does not exist
                self.functions[o] = getattr(self, nt_to_fun(o))
            except AttributeError:
                self.functions[o] = self.walk_error

    def set_function(self, function, *node_types):
        """Overrides the default walking function for each of the specified
        node_types with the given function
        """
        from warnings import warn
        warn("Instance-based walkers (<=0.6.0) walkers are deprecated. "
             "You should use new-style/class based walkers", stacklevel=2)
        for nt in node_types:
            self.functions[nt] = function

    @classmethod
    def set_handler(cls, function, *node_types):
        """Associate in cls the given function to the given node_types."""
        for nt in node_types:
            setattr(cls, nt_to_fun(nt), function)

    @classmethod
    def super(cls, self, formula, *args, **kwargs):
        """Call the correct walk_* function of cls for the given formula."""
        f = getattr(cls, nt_to_fun(formula.node_type()))
        return f(self, formula, *args, **kwargs)

    @handles(op.ALL_TYPES)
    def walk_error(self, formula, **kwargs):
        """Default function for a node that is not handled by the Walker.

        This tries to handle the node using the Dynamic Walker
        Function information from the environment. If this fails, then
        an UnsupportedOperatorError exception is given.

        """
        node_type = formula.node_type()
        if node_type in self.env.dwf:
            dwf = self.env.dwf[node_type]
            walker_class = type(self)
            if type(self) in dwf:
                self.functions[node_type] = partial(dwf[walker_class], self)
                return self.functions[node_type](formula, **kwargs)

        node_type = formula.node_type()
        raise pysmt.exceptions.UnsupportedOperatorError(node_type=node_type,
                                                        expression=formula)

# EOC Walker
