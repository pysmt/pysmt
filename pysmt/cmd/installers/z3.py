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
import platform

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class Z3Installer(SolverInstaller):

    SOLVER = "z3"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, osx=None, git_version=None):
        arch = self.architecture
        if arch == "x86_64":
            arch = "x64"

        system = self.os_name
        if system == "linux":
            system = "ubuntu-14.04"
        elif system == "darwin":
            system = "osx-%s" % osx
        elif system == "windows":
            system = "win"

        # Stable versions template
        # archive_name = "z3-%s-%s-%s.zip" % (solver_version, arch, system)
        #
        # Nightly build template
        archive_name = "z3-%s.%s-%s-%s.zip" % (solver_version, git_version, arch, system)
        native_link = "https://github.com/pysmt/Z3bin/blob/master/nightly/{archive_name}?raw=true"

        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)

    def move(self):
        bpath = os.path.join(self.extract_path, "bin")
        files = ["python/z3"]
        if self.os_name == "linux":
            files += [ "libz3.so" ]
        elif self.os_name == "darwin":
            files += [ "libz3.a", "libz3.dylib" ]
        elif self.os_name == "windows":
            files += [ "libz3.dll", "libz3.lib" ]

        for f in files:
            SolverInstaller.mv(os.path.join(bpath, f), self.bindings_dir)

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "z3")
