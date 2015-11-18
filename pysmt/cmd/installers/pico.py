# Copyright 2014 Andrea Micheli and Marco Gario
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
import sys
import pip

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class PicoSATInstaller(SolverInstaller):

    SOLVER = "picosat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 mirror_link=mirror_link)

    def download(self):
        pass # Nothing to download

    def unpack(self):
        pass # Nothing to unpack

    def compile(self):
        pip.main(['install', '--target', self.bindings_dir, 'pypicosat'])

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import picosat
                return picosat.picosat_version()
            except ImportError:
                if "picosat" in sys.modules:
                    del sys.modules["picosat"]
                return None
