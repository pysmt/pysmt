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
import platform

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class MSatCFFIInstaller(SolverInstaller):

    SOLVER = "msat-cffi"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        archive_name = "mathsat-%s-%s-%s.tar.gz" % (solver_version,
                                                    self.os_name,
                                                    self.architecture)
        if self.os_name == "darwin":
            raise ValueError("CFFI is currently supported on linux only")
        native_link = "http://mathsat.fbk.eu/download.php?file={archive_name}"

        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link = native_link,
                                 mirror_link=mirror_link)

        self.python_bindings_dir = os.path.join(self.extract_path, "python")
        self.libmathsat_dir = os.path.join(self.extract_path, "libmathsat")

    def compile(self):
        self.clean_dir(self.libmathsat_dir)
        SolverInstaller.run("ar -x ../lib/libmathsat.a", self.libmathsat_dir)
        SolverInstaller.run("gcc -shared *.o "\
                            "-lgmp -lgmpxx -lstdc++ "\
                            "-o libmathsat.so",
                            self.libmathsat_dir)
        revision = "ec7b8425a701b59e469b3e46c2437faa51d2be69"
        self.do_download("https://raw.githubusercontent.com/pysmt/mathsat-cffi/%s/mathsat_cffi.py" % revision,
                         os.path.join(self.libmathsat_dir, "mathsat_cffi.py"))

    def move(self):
        SolverInstaller.mv(os.path.join(self.libmathsat_dir, "libmathsat.so"),
                           self.bindings_dir)
        SolverInstaller.mv(os.path.join(self.libmathsat_dir, "mathsat_cffi.py"),
                           self.bindings_dir)

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            version = None
            try:
                from mathsat_cffi import mathsat
                version_str = mathsat.msat_get_version()
                m = re.match(r"^MathSAT5 version (\d+\.\d+\.\d+) .*$", version_str)
                if m is not None:
                    version = m.group(1)
            finally:
                if "mathsat_cffi" in sys.modules:
                    del sys.modules["mathsat_cffi"]
                # Return None, without raising an exception
                # pylint: disable=lost-exception
                return version
