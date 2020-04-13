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
import glob

from pysmt.cmd.installers.base import SolverInstaller


class Z3Installer(SolverInstaller):

    SOLVER = "z3"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, osx=None, git_version=None, commit=None):
        arch = self.architecture
        if arch == "x86_64":
            arch = "x64"

        system = self.os_name
        if system == "linux":
            system = "ubuntu-16.04"
        elif system == "darwin":
            system = "osx-%s" % osx
        elif system == "windows":
            system = "win"

        if git_version is None:
            # Stable versions template
            if commit:
                archive_name = "z3-%s.%s-%s-%s.zip" % (solver_version, commit, arch, system)
            else:
                archive_name = "z3-%s-%s-%s.zip"  % (solver_version, arch, system)
            native_link = "https://github.com/Z3Prover/z3/releases/download/z3-" + solver_version + "/{archive_name}"
            # print(native_link)
        else:
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
        libfiles = []
        if self.os_name == "linux":
            libfiles += glob.glob(bpath + '/*.so')
        elif self.os_name == "darwin":
            libfiles += glob.glob(bpath + '/*.a')
            libfiles += glob.glob(bpath + '/*.dylib')
        elif self.os_name == "windows":
            libfiles += glob.glob(bpath + '/*.dll')
            libfiles += glob.glob(bpath + '/*.lib')

        SolverInstaller.mv(os.path.join(bpath, "python/z3"), self.bindings_dir)

        # z3 will check for shared libraries in z3/lib, before builtins.Z3_LIB_DIRS,
        # and Z3_LIBRARY_PATH env var lookup (or OS-level LD_LIBRARY_PATH)
        # (see z3/z3core.py)
        libpath = os.path.join(self.bindings_dir, "z3/lib/")
        if not os.path.exists(libpath):
            os.mkdir(libpath)

        for f in libfiles:
            SolverInstaller.mv(f, libpath)

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "z3")
