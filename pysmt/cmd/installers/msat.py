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


class MSatInstaller(SolverInstaller):

    SOLVER = "msat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):

        # Getting the right archive name
        archive_name_template = "mathsat-{version}-{os}-{arch}.{ext}"
        format = {
                "version": solver_version,
                "os" : self.os_name,
                "arch": self.architecture,
                "ext": "tar.gz"
        }
        if self.os_name == "windows":
            format["ext"] = "zip"
            format["arch"] = "msvc"
            format["os"] = "win64" if self.architecture == "x86_64" else "win32"
        elif self.os_name == "darwin":
            # Since version 5.6.7 the architecture is not included in the
            # pkg name for the OSX release as it is considered a "univeral binary"
            archive_name_template = "mathsat-{version}-{os}.{ext}"
            format["os"] = "osx"

        archive_name = archive_name_template.format(**format)

        native_link = "http://mathsat.fbk.eu/download.php?file={archive_name}"

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
            setup_py_win_url = "https://github.com/pysmt/solvers_patches/raw/master/mathsat/setup-win.py"

            SolverInstaller.do_download(gmp_h_url, os.path.join(incdir, "gmp.h"))
            SolverInstaller.do_download(mpir_dll_url, os.path.join(libdir, "mpir.dll"))
            SolverInstaller.do_download(mpir_lib_url, os.path.join(libdir, "mpir.lib"))

            # Overwrite setup.py with the patched version
            setup_py = os.path.join(self.python_bindings_dir, "setup.py")
            SolverInstaller.mv(setup_py, setup_py + ".original")
            SolverInstaller.do_download(setup_py_win_url, setup_py)

        # Run setup.py to compile the bindings
        if self.os_name in {"windows", "darwin"}:
            SolverInstaller.run_python("./setup.py build_ext", self.python_bindings_dir)
        else:
            # NB: -R adds --rpath=$ORIGIN to link step, which makes shared library object
            # searched for in the extension's directory (no need for LD_LIBRARY_PATH)
            # (note: this is the default behavior for DLL discovery on Windows)
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
        SolverInstaller.mv(os.path.join(pdir, "mathsat.py"), self.bindings_dir)

        # Since MathSAT 5.5.0 we also need the SO/DLL/DYLIB of mathsat in the PATH
        # Under Windows, we also need the DLLs of MPIR in the PATH
        for f in os.listdir(libdir):
            if f.endswith(".so") or f.endswith(".dll") or f.endswith(".dylib"):
                SolverInstaller.mv(os.path.join(libdir, f), self.bindings_dir)

        # Fix issue in MathSAT 5.5.1 linking to incorrect directory on OSX
        if self.os_name == "darwin":
            soname = glob.glob(self.bindings_dir + "/_mathsat*.so")[0]
            old_path = "/Users/alb/src/build_mathsat5/opt/libmathsat.dylib"
            new_path = "%s/libmathsat.dylib" % self.bindings_dir
            SolverInstaller.run("install_name_tool -change %s %s %s" %
                                (old_path, new_path, soname))


    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "msat")
