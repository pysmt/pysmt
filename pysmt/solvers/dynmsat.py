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

class MSATWrapper(object):

    def __init__(self, *args, **kwargs):
        self._msat_wrapper = self.get_lib()

    def get_lib_name(self):
        return "mathsat"

    def get_lib(self):
        try:
            lib_name = self.get_lib_name()
            return importlib.import_module(lib_name)
        except (ModuleNotFoundError, ImportError):
            raise SolverAPINotFound


class OptiMSATWrapper(MSATWrapper):

    def __init__(self, *args, **kwargs):
        super(OptiMSATWrapper, self).__init__(*args, **kwargs)

    def get_lib_name(self):
        return "optimathsat"
