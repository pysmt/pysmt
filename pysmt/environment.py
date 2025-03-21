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
from __future__ import annotations
from typing import TYPE_CHECKING
if TYPE_CHECKING:
    from typing import Self, Optional

from pysmt.simplifier import Simplifier
from pysmt.printers import HRSerializer
from pysmt.substituter import Substituter, MGSubstituter
from pysmt.type_checker import SimpleTypeChecker
from pysmt.oracles import (QuantifierOracle, TheoryOracle, FreeVarsOracle,
                           SizeOracle, AtomsOracle, TypesOracle)
from pysmt.formula import FormulaManager
from pysmt.factory import Factory
from pysmt.typing import TypeManager


class Environment(object):
    """The Environment provides global singleton instances of various objects.

    FormulaManager and the TypeChecker are among the most commonly used ones.

    Subclasses of Environment should take care of adjusting the list
    of classes for the different services, by changing the class
    attributes.
    """
    TypeCheckerClass = SimpleTypeChecker
    FormulaManagerClass = FormulaManager
    TypeManagerClass = TypeManager
    SimplifierClass = Simplifier
    #SubstituterClass = pysmt.substituter.MSSubstituter
    SubstituterClass = MGSubstituter
    HRSerializerClass = HRSerializer
    QuantifierOracleClass = QuantifierOracle
    TheoryOracleClass = TheoryOracle
    FreeVarsOracleClass = FreeVarsOracle
    SizeOracleClass = SizeOracle
    AtomsOracleClass = AtomsOracle
    TypesOracleClass = TypesOracle

    def __init__(self: Self) -> None:
        self._stc: SimpleTypeChecker = self.TypeCheckerClass(self)
        self._formula_manager: FormulaManager = self.FormulaManagerClass(self)
        # NOTE: Both Simplifier and Substituter keep an internal copy
        # of the Formula Manager and need to be initialized afterwards
        self._simplifier: Simplifier = self.SimplifierClass(self)
        self._substituter: Substituter = self.SubstituterClass(self)
        self._serializer: HRSerializer = self.HRSerializerClass(self)
        self._qfo: QuantifierOracle = self.QuantifierOracleClass(self)
        self._theoryo: TheoryOracle = self.TheoryOracleClass(self)
        self._fvo: FreeVarsOracle = self.FreeVarsOracleClass(self)
        self._sizeo: SizeOracle = self.SizeOracleClass(self)
        self._ao: AtomsOracle = self.AtomsOracleClass(self)
        self._typeso: TypesOracle = self.TypesOracleClass(self)
        self._type_manager: TypeManager = self.TypeManagerClass(self)

        self._factory: Optional[Factory] = None
        # Configurations
        self.enable_infix_notation: bool = False
        self.enable_div_by_0: bool = True

        # This option allows the construction of a symbol with empty
        # name (i.e. `Symbol("", INT)`). This feature is allowed by
        # SmtLib, but not all solvers support this and the machinery
        # needed to rename this one symbol is simply not worth the
        # effort given that such a name is simply bad
        # practice. However to validate pathological models we can
        # allow this on the pysmt side to use walkers
        # (e.g. substitution and simplification).
        self.allow_empty_var_names: bool = False

        # Dynamic Walker Configuration Map
        # See: add_dynamic_walker_function
        self.dwf: dict = {}

    @property
    def formula_manager(self) -> FormulaManager:
        return self._formula_manager

    @property
    def type_manager(self: Self) -> TypeManager:
        return self._type_manager

    @property
    def simplifier(self: Self) -> Simplifier:
        return self._simplifier

    @property
    def serializer(self: Self) -> HRSerializer:
        return self._serializer

    @property
    def substituter(self: Self) -> Substituter:
        return self._substituter

    @property
    def stc(self: Self) -> SimpleTypeChecker:
        """ Get the Simple Type Checker """
        return self._stc

    @property
    def qfo(self: Self) -> QuantifierOracle:
        """ Get the Quantifier Oracle """
        return self._qfo

    @property
    def ao(self: Self) -> AtomsOracle:
        """ Get the Atoms Oracle """
        return self._ao

    @property
    def theoryo(self: Self) -> TheoryOracle:
        """ Get the Theory Oracle """
        return self._theoryo

    @property
    def typeso(self: Self) -> TypesOracle:
        """ Get the Types Oracle """
        return self._typeso

    @property
    def fvo(self: Self) -> FreeVarsOracle:
        """ Get the FreeVars Oracle """
        return self._fvo

    @property
    def sizeo(self: Self) -> SizeOracle:
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
    def factory(self: Self) -> Factory:
        if self._factory is None:
            self._factory = Factory(self)
        return self._factory

    def __enter__(self: Self) -> Self:
        """Entering a Context """
        push_env(self)
        return self

    def __exit__(self: Self, exc_type, exc_val, exc_tb) -> None:
        """Remove environment from global stack."""
        pop_env()

# EOC Environment

#### GLOBAL ENVIRONMENTS STACKS ####
ENVIRONMENTS_STACK: list[Environment] = []

def get_env() -> Environment:
    """Returns the Environment at the head of the stack."""
    return ENVIRONMENTS_STACK[-1]

def push_env(env: Optional[Environment] = None) -> None:
    """Push a env in the stack. If env is None, a new Environment is created."""
    if env is None:
        env = Environment()
    ENVIRONMENTS_STACK.append(env)

def pop_env() -> Environment:
    """Pop an env from the stack."""
    return ENVIRONMENTS_STACK.pop()

def reset_env() -> Environment:
    """Destroys and recreate the head environment."""
    pop_env()
    push_env()
    return get_env()

# Create the default environment
push_env()
