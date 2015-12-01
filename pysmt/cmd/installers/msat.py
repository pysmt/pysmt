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

import os
import re
import sys

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class MSatInstaller(SolverInstaller):

    SOLVER = "msat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        archive_name = "mathsat-%s-%s-%s.tar.gz" % (solver_version,
                                                    self.os_name,
                                                    self.architecture)
        native_link = "http://mathsat.fbk.eu/download.php?file={archive_name}"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link = native_link,
                                 mirror_link=mirror_link)

        self.python_bindings_dir = os.path.join(self.extract_path, "python")


    def compile(self):
        SolverInstaller.run_python("./setup.py build", self.python_bindings_dir)


    def move(self):
        libdir = "lib.%s-%s-%s" % (self.os_name, self.architecture,
                                   self.python_version)
        pdir = self.python_bindings_dir
        bdir = os.path.join(pdir, "build")
        sodir = os.path.join(bdir, libdir)

        for f in os.listdir(sodir):
            if f.endswith(".so"):
                SolverInstaller.mv(os.path.join(sodir, f), self.bindings_dir)
        SolverInstaller.mv(os.path.join(pdir, "mathsat.py"), self.bindings_dir)


    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import mathsat
                version_str = mathsat.msat_get_version()
                m = re.match(r"^MathSAT5 version (\d+\.\d+\.\d+) .*$", version_str)
                if m is None:
                    return None
                return m.group(1)
            except ImportError:
                if "mathsat" in sys.modules:
                    del sys.modules["mathsat"]
                return None
