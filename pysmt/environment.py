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
"""
The Environment is a key structure in pySMT. It contains multiple
singleton objects that are used throughout the system, such as the
FormulaManager, Simplifier, HRSerializer, SimpleTypeChecker.
"""

import pysmt.simplifier
import pysmt.printers
import pysmt.substituter
import pysmt.type_checker
import pysmt.oracles
import pysmt.formula
import pysmt.factory
import pysmt.decorators
import pysmt.typing


class Environment(object):
    """The Environment provides global singleton instances of various objects.

    FormulaManager and the TypeChecker are among the most commonly used ones.

    Subclasses of Environment should take care of adjusting the list
    of classes for the different services, by changing the class
    attributes.
    """
    TypeCheckerClass = pysmt.type_checker.SimpleTypeChecker
    FormulaManagerClass = pysmt.formula.FormulaManager
    TypeManagerClass = pysmt.typing.TypeManager
    SimplifierClass = pysmt.simplifier.Simplifier
    #SubstituterClass = pysmt.substituter.MSSubstituter
    SubstituterClass = pysmt.substituter.MGSubstituter
    HRSerializerClass = pysmt.printers.HRSerializer
    QuantifierOracleClass = pysmt.oracles.QuantifierOracle
    TheoryOracleClass = pysmt.oracles.TheoryOracle
    FreeVarsOracleClass= pysmt.oracles.FreeVarsOracle
    SizeOracleClass = pysmt.oracles.SizeOracle
    AtomsOracleClass = pysmt.oracles.AtomsOracle
    TypesOracleClass = pysmt.oracles.TypesOracle

    def __init__(self):
        self._stc = self.TypeCheckerClass(self)
        self._formula_manager = self.FormulaManagerClass(self)
        # NOTE: Both Simplifier and Substituter keep an internal copy
        # of the Formula Manager and need to be initialized afterwards
        self._simplifier = self.SimplifierClass(self)
        self._substituter = self.SubstituterClass(self)
        self._serializer = self.HRSerializerClass(self)
        self._qfo = self.QuantifierOracleClass(self)
        self._theoryo = self.TheoryOracleClass(self)
        self._fvo = self.FreeVarsOracleClass(self)
        self._sizeo = self.SizeOracleClass(self)
        self._ao = self.AtomsOracleClass(self)
        self._typeso = self.TypesOracleClass(self)
        self._type_manager = self.TypeManagerClass(self)

        self._factory = None
        # Configurations
        self.enable_infix_notation = False
        self.enable_div_by_0 = True

        # Dynamic Walker Configuration Map
        # See: add_dynamic_walker_function
        self.dwf = {}

    @property
    def formula_manager(self):
        return self._formula_manager

    @property
    def type_manager(self):
        return self._type_manager

    @property
    def simplifier(self):
        return self._simplifier

    @property
    def serializer(self):
        return self._serializer

    @property
    def substituter(self):
        return self._substituter

    @property
    def stc(self):
        """ Get the Simple Type Checker """
        return self._stc

    @property
    def qfo(self):
        """ Get the Quantifier Oracle """
        return self._qfo

    @property
    def ao(self):
        """ Get the Atoms Oracle """
        return self._ao

    @property
    def theoryo(self):
        """ Get the Theory Oracle """
        return self._theoryo

    @property
    def typeso(self):
        """ Get the Types Oracle """
        return self._typeso

    @property
    def fvo(self):
        """ Get the FreeVars Oracle """
        return self._fvo

    @property
    def sizeo(self):
        """ Get the Size Oracle """
        return self._sizeo

    def add_dynamic_walker_function(self, nodetype, walker, function):
        """Dynamically bind the given function to the walker for the nodetype.

        This function enables the extension of walkers for new
        nodetypes. When introducing a new nodetype, we link a new
        function to a given walker, so that the walker will be able to
        handle the new nodetype.

        See :py:meth:`pysmt.walkers.generic.Walker.walk_error` for
        more information.
        """
        # self.dwf is a map of maps: {nodetype, {walker: function}}
        if nodetype not in self.dwf:
            self.dwf[nodetype] = {}

        assert walker not in self.dwf[nodetype], "Redefinition"
        self.dwf[nodetype][walker] = function

    @property
    def factory(self):
        if self._factory is None:
            self._factory = pysmt.factory.Factory(self)
        return self._factory

    def __enter__(self):
        """Entering a Context """
        push_env(self)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Remove environment from global stack."""
        pop_env()

# EOC Environment

#### GLOBAL ENVIRONMENTS STACKS ####
ENVIRONMENTS_STACK = []

def get_env():
    """Returns the Environment at the head of the stack."""
    return ENVIRONMENTS_STACK[-1]

def push_env(env=None):
    """Push a env in the stack. If env is None, a new Environment is created."""
    if env is None:
        env = Environment()
    ENVIRONMENTS_STACK.append(env)

def pop_env():
    """Pop an env from the stack."""
    return ENVIRONMENTS_STACK.pop()

def reset_env():
    """Destroys and recreate the head environment."""
    pop_env()
    push_env()
    return get_env()

# Create the default environment
push_env()
