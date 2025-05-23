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

from pysmt.exceptions import SolverAPINotFound

import importlib

def MSATLibLoader(name):
    if name not in ["mathsat", "optimathsat"]:
        raise ValueError(name)

    try:
        return importlib.import_module(name)
    except ImportError:
        raise SolverAPINotFound

def MSATCreateEnv(name, msat_config):
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

    return EnvClass(msat_config)

def MSATCreateConverter(name, environment, msat_env):
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

    ConvClass = getattr(importlib.import_module(map[name]["lib"]), map[name]["class"])

    return ConvClass(environment, msat_env)
