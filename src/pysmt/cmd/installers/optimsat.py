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

from pysmt.cmd.installers.base import SolverInstaller
from pysmt.cmd.installers.msat import MathSATFamilyInstaller


class OptiMSatInstaller(MathSATFamilyInstaller):
    SOLVER = "optimsat"
    MODULE = "optimathsat"

    def __init__(self, install_dir, target, solver_version, mirror_link=None):

        # Getting the right archive name
        archive_name_template = "optimathsat-{version}-{os}-{arch}.{ext}"
        format = {
            "version": solver_version,
            "os": self.os_name,
            "arch": self.architecture,
            "ext": "tar.gz",
        }
        if self.os_name in ["windows", "darwin"]:
            # Since version 1.7.5 the architecture is not included in the
            # pkg name for the OSX and Win release as it is considered a "universal binary"
            archive_name_template = "optimathsat-{version}-{os}.{ext}"
        if self.os_name == "windows":
            format["ext"] = "zip"
            format["os"] = "win64" if self.architecture == "x86_64" else "win32"
        elif self.os_name == "darwin":
            format["os"] = "osx"

        archive_name = archive_name_template.format(**format)

        native_link = (
            "https://optimathsat.disi.unitn.it/releases/optimathsat-%s/{archive_name}"
            % solver_version
        )

        MathSATFamilyInstaller.__init__(
            self,
            install_dir=install_dir,
            target=target,
            solver_version=solver_version,
            archive_name=archive_name,
            native_link=native_link,
            mirror_link=mirror_link,
        )

    def compile(self):
        if self.os_name == "windows":
            libdir = os.path.join(self.python_bindings_dir, "../lib")
            incdir = os.path.join(self.python_bindings_dir, "../include")
            gmp_h_url = "https://github.com/mikand/tamer-windows-deps/raw/master/gmp/include/gmp.h"
            mpir_dll_url = (
                "https://github.com/Legrandin/mpir-windows-builds/blob/master/mpir-2.6.0_VS2015_%s/mpir.dll?raw=true"
                % self.bits
            )
            mpir_lib_url = (
                "https://github.com/Legrandin/mpir-windows-builds/blob/master/mpir-2.6.0_VS2015_%s/mpir.lib?raw=true"
                % self.bits
            )

            SolverInstaller.do_download(gmp_h_url, os.path.join(incdir, "gmp.h"))
            SolverInstaller.do_download(mpir_dll_url, os.path.join(libdir, "mpir.dll"))
            SolverInstaller.do_download(mpir_lib_url, os.path.join(libdir, "mpir.lib"))

        MathSATFamilyInstaller.compile(self)
