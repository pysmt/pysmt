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


from typing import Any, Optional
import importlib

import pysmt
from pysmt.environment import Environment
from pysmt.exceptions import SolverAPINotFound

def MSATLibLoader(name):
    if name not in ["mathsat", "optimathsat"]:
        raise ValueError(name)

    try:
        return importlib.import_module(name)
    except ImportError:
        raise SolverAPINotFound

def _native_root(name: str, environment: Optional[Environment]) -> Optional["pysmt.solvers.msat.MSatEnv"]:
    """Returns the root MSatEnv of a native MathSAT environment, if any."""
    if name != "mathsat" or environment is None:
        return None
    return getattr(environment.formula_manager, "msat_root", None)

def MSATCreateEnv(name: str, msat_config: Any, environment: Optional[Environment]=None) -> "pysmt.solvers.msat.MSatEnv":
    map = {
        "mathsat" : {
            "class" : "MSatEnv",
            "lib"   : "pysmt.solvers.msat"
        },
        "optimathsat": {
            "class" : "OptiMSATEnv",
            "lib"   : "pysmt.optimization.optimsat"
        }
    }
    if name not in map.keys():
        raise ValueError(name)

    EnvClass = getattr(importlib.import_module(map[name]["lib"]), map[name]["class"])

    root = _native_root(name, environment)
    if root is not None:
        return EnvClass(msat_config, sibling=root)
    return EnvClass(msat_config)

def MSATCreateConverter(name: str, environment: Environment, msat_env: "pysmt.solvers.msat.MSatEnv") -> "pysmt.solvers.msat.MSatConverter":
    map = {
        "mathsat" : {
            "class" : "MSatConverter",
            "lib"   : "pysmt.solvers.msat"
        },
        "optimathsat": {
            "class" : "OptiMSATConverter",
            "lib"   : "pysmt.optimization.optimsat"
        }
    }
    if name not in map.keys():
        raise ValueError(name)

    if _native_root(name, environment) is not None:
        map[name] = {"class": "NativeMSatConverter", "lib": "pysmt.native.msat"}

    ConvClass = getattr(importlib.import_module(map[name]["lib"]), map[name]["class"])

    return ConvClass(environment, msat_env)
