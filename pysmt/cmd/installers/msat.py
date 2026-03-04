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
            archive_name_template = "mathsat-{version}-{os}.{ext}"
            format["ext"] = "zip"
            format["os"] = "win64"
        elif self.os_name == "darwin":
            # Since version 5.6.7 the architecture is not included in the
            # pkg name for the OSX release as it is considered a "univeral binary"
            archive_name_template = "mathsat-{version}-{os}.{ext}"
            format["os"] = "macos"

        archive_name = archive_name_template.format(**format)

        native_link = "https://mathsat.fbk.eu/release/{archive_name}"

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

            gmp_win_url = "https://github.com/apotocki/gmp-win/releases/download/6.3.0/gmp-6.3.0.zip"
            gmp_archive = os.path.join(self.base_dir, "gmp-6.3.0.zip")
            gmp_dir = os.path.join(self.base_dir, "gmp-6.3.0")
            SolverInstaller.clean_dir(gmp_dir)
            SolverInstaller.do_download(url=gmp_win_url, file_name=gmp_archive)
            SolverInstaller.unzip(gmp_archive, gmp_dir)

            gmp_include_dir = os.path.join(self.base_dir, "gmp-6.3.0", "include")
            gmp_lib_dir = os.path.join(self.base_dir, "gmp-6.3.0", "lib")
            # gmp_dll_dir = os.path.join(self.base_dir, "gmp-6.3.0", "bin")
            SolverInstaller.mv(os.path.join(gmp_include_dir, "gmp.h"), incdir)
            SolverInstaller.mv(source=os.path.join(gmp_lib_dir, "gmpdll.lib"),
                               dest=os.path.join(libdir, "gmp.lib"))

            # The MathSAT setup.py expects to link against "mpir" on Windows,
            # but we link against "gmp", so we need to patch the setup.py
            setup_py_path = os.path.join(self.python_bindings_dir, "setup.py")
            SolverInstaller.replace_in_file(setup_py_path, "mpir", "gmp")

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
        libdir = os.path.join(self.python_bindings_dir, "../bin")

        # First, we need the SWIG-generated wrapper
        for f in os.listdir(sodir):
            if "_mathsat" in f:
                SolverInstaller.mv(os.path.join(sodir, f), self.bindings_dir)
        SolverInstaller.mv(os.path.join(pdir, "mathsat.py"), self.bindings_dir)

        # Since MathSAT 5.5.0 we also need the SO/DLL/DYLIB of mathsat in the PATH
        # Under Windows, we also need the DLLs of MPIR in the PATH
        for f in os.listdir(libdir):
            if f.endswith(".so") or f.endswith(".dll") or f.endswith(".dylib"):
                SolverInstaller.mv(os.path.join(libdir, f), self.bindings_dir)

        # Fix issue in MathSAT 5.6.10 linking to incorrect directory on MacOS
        if self.os_name == "darwin":
            soname = glob.glob(self.bindings_dir + "/_mathsat*.so")[0]
            old_path = "/Users/alb/src/release/build/libmathsat.dylib"
            new_path = "%s/libmathsat.dylib" % self.bindings_dir
            SolverInstaller.run("install_name_tool -change %s %s %s" %
                                (old_path, new_path, soname))


    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "msat")
