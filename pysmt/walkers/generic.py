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
import sys
from pysmt.fnode import FNode
from typing import Any, Callable, Dict, List, Optional, Tuple, Type, Union, cast, Iterable

if sys.version_info >= (3, 3):
    from collections.abc import Iterable as CollectionsIterable
else:
    from collections import Iterable as CollectionsIterable

import pysmt.operators as op
import pysmt.exceptions

# NodeType to Function Name
def nt_to_fun(o: int) -> str:
    """Returns the name of the walk function for the given nodetype."""
    return "walk_%s" % op.op_to_str(o).lower()

class handles(object):
    """Decorator for walker functions.

    Use it by specifying the nodetypes that need to be handled by the
    given function. It is possible to use grouped (e.g., op.RELATIONS)
    directly. ::

      @handles(op.NODE, ...)
      def walk_special(...):
         ...

    """
    def __init__(self, *nodetypes: Union[int, Iterable[int]]):
        if len(nodetypes) == 1 and isinstance(nodetypes[0], CollectionsIterable):
            nt: Iterable[int] = nodetypes[0]
        else:
            assert all(isinstance(x, int) for x in nodetypes)
            nt = cast(Tuple[int], nodetypes)
        self.nodetypes: List[int] = list(cast(Iterable[int], nt))

    def __call__(self, func: Callable) -> Callable:
        nodetypes = self.nodetypes
        if hasattr(func, "nodetypes"):
            nodetypes = cast(List[int], getattr(func, "nodetypes")) + nodetypes
        setattr(func, "nodetypes", nodetypes)
        return func

class MetaNodeTypeHandler(type):
    """Metaclass used to intepret the nodehandler decorator. """
    def __new__(cls: Type["MetaNodeTypeHandler"], name: str, bases: Any, dct: Dict[str, Any]) -> Any:
        obj = type.__new__(cls, name, bases, dct)
        for k, v in dct.items():
            if hasattr(v, "nodetypes"):
                cast("Walker", obj).set_handler(v, *cast(List[int], getattr(v, "nodetypes")))
        return obj


class Walker(object, metaclass=MetaNodeTypeHandler):
    """Base Abstract Walker class.

    Do not subclass directly, use DagWalker or TreeWalker, instead.
    """

    def __init__(self, env: Optional["pysmt.environment.Environment"]=None):
        if env is None:
            import pysmt.environment
            env = pysmt.environment.get_env()
        self.env: "pysmt.environment.Environment" = env

    def set_function(self, function, *node_types):
        """Instance-based walkers (<=0.6.0) are no longer supported.

        Use class-based walkers instead: define walk_* methods (or use
        the ``@handles`` decorator) on a subclass.
        """
        raise NotImplementedError(
            "Instance-based walkers (<=0.6.0) are deprecated. "
            "You should use new-style/class based walkers.")

    @classmethod
    def set_handler(cls, function: Callable, *node_types):
        """Associate in cls the given function to the given node_types."""
        for nt in node_types:
            setattr(cls, nt_to_fun(nt), function)

    @classmethod
    def super(cls, self, formula: FNode, *args, **kwargs) -> Any:
        """Call the correct walk_* function of cls for the given formula.

        The return type depends on the walker: an FNode for rewriting
        walkers, but a generator (TreeWalker), a set or an int (oracles),
        etc. for others; hence Any.
        """
        nt = formula.node_type()
        try:
            f = getattr(cls, nt_to_fun(nt))
        except AttributeError:
            # Custom node types (see new_node_type) have no walk_* method
            # on the class. Look for a handler registered on this walker's
            # environment via add_dynamic_walker_function; keeping the
            # lookup env-local is what stops registrations from leaking
            # across environments.
            fun = self.env.get_dynamic_walker_function(nt, cls)
            if fun is None:
                raise pysmt.exceptions.UnsupportedOperatorError(
                    node_type=nt, expression=formula)
            return fun(self, formula, *args, **kwargs)
        return f(self, formula, *args, **kwargs)

    @handles(op.ALL_TYPES)
    def walk_error(self, formula, **kwargs):
        """Default function for a node that is not handled by the Walker."""
        node_type = formula.node_type()
        raise pysmt.exceptions.UnsupportedOperatorError(node_type=node_type,
                                                        expression=formula)

# EOC Walker
