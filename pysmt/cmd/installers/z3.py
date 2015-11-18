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
from __future__ import absolute_import

import os
import sys

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class Z3Installer(SolverInstaller):

    SOLVER = "z3"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        arch = self.architecture
        if arch == "x86_64":
            arch = "x64"

        system = self.os_name
        if system == "linux":
            system = "ubuntu-14.04"

        archive_name = "z3-%s-%s-%s.zip" % (solver_version, arch, system)
        native_link = "https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/{archive_name}"

        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)


    def move(self):
        bpath = os.path.join(self.extract_path, "bin")
        files = ["libz3.so",
                 "z3consts.py",
                 "z3core.py",
                 "z3num.py",
                 "z3poly.py",
                 "z3printer.py",
                 "z3.py",
                 "z3rcf.py",
                 "z3test.py",
                 "z3types.py",
                 "z3util.py"]
        for f in files:
            SolverInstaller.mv(os.path.join(bpath, f), self.bindings_dir)

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import z3
                (major, minor, ver, _) = z3.get_version()
                return "%d.%d.%d" % (major, minor, ver)
            except ImportError:
                if "z3" in sys.modules:
                    del sys.modules["z3"]
                return None
        return None
