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
import glob

from pysmt.cmd.installers.base import SolverInstaller


class OptiMSatInstaller(SolverInstaller):

    SOLVER = "optimsat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):

        # Getting the right archive name
        archive_name_template = "optimathsat-{version}-{os}-{arch}.{ext}"
        format = {
                "version": solver_version,
                "os" : self.os_name,
                "arch": self.architecture,
                "ext": "tar.gz"
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

        native_link = "https://optimathsat.disi.unitn.it/releases/optimathsat-%s/{archive_name}" % solver_version

        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link = native_link,
                                 mirror_link=mirror_link)

        self.python_bindings_dir = os.path.join(self.extract_path, "python")


    def compile(self):
        if self.os_name == "windows":
            libdir = os.path.join(self.python_bindings_dir, "../lib")
            incdir = os.path.join(self.python_bindings_dir, "../include")
            gmp_h_url = "https://github.com/mikand/tamer-windows-deps/raw/master/gmp/include/gmp.h"
            mpir_dll_url = "https://github.com/Legrandin/mpir-windows-builds/blob/master/mpir-2.6.0_VS2015_%s/mpir.dll?raw=true" % self.bits
            mpir_lib_url = "https://github.com/Legrandin/mpir-windows-builds/blob/master/mpir-2.6.0_VS2015_%s/mpir.lib?raw=true" % self.bits

            SolverInstaller.do_download(gmp_h_url, os.path.join(incdir, "gmp.h"))
            SolverInstaller.do_download(mpir_dll_url, os.path.join(libdir, "mpir.dll"))
            SolverInstaller.do_download(mpir_lib_url, os.path.join(libdir, "mpir.lib"))

        if self.os_name in {"darwin"}:
            SolverInstaller.run_python("./setup.py build_ext", self.python_bindings_dir)
        else:
            SolverInstaller.run_python("./setup.py build_ext -R $ORIGIN", self.python_bindings_dir)


    def move(self):
        pdir = self.python_bindings_dir
        bdir = os.path.join(pdir, "build")
        sodir = glob.glob(bdir + "/lib.*")[0]
        libdir = os.path.join(self.python_bindings_dir, "../lib")

        # First, we need the SWIG-generated wrapper
        for f in os.listdir(sodir):
            if f.endswith(".so") or f.endswith(".pyd"):
                SolverInstaller.mv(os.path.join(sodir, f), self.bindings_dir)
        SolverInstaller.mv(os.path.join(pdir, "optimathsat.py"), self.bindings_dir)

        # Since MathSAT 5.5.0 we also need the SO/DLL/DYLIB of mathsat in the PATH
        # Under Windows, we also need the DLLs of MPIR in the PATH
        for f in os.listdir(libdir):
            if f.endswith(".so") or f.endswith(".dll") or f.endswith(".dylib"):
                SolverInstaller.mv(os.path.join(libdir, f), self.bindings_dir)

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "optimsat")
