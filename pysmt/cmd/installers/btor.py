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
import os

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class BtorInstaller(SolverInstaller):

    SOLVER = "btor"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, lingeling_version=None):
        archive_name = "boolector-%s-with-lingeling-%s.tar.bz2" % \
                       (solver_version, lingeling_version)
        native_link = "http://fmv.jku.at/boolector/{archive_name}"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)


    def compile(self):
        # First build
        SolverInstaller.run("make", directory=self.extract_path)

        # Reconfigure and build python bindings
        SolverInstaller.run("bash ./configure.sh -fPIC",
                          directory=os.path.join(self.extract_path, "lingeling"))
        SolverInstaller.run("make",
                          directory=os.path.join(self.extract_path, "lingeling"))

        SolverInstaller.run("bash ./configure -python",
                          directory=os.path.join(self.extract_path, "boolector"))
        SolverInstaller.run("make",
                          directory=os.path.join(self.extract_path, "boolector"))


    def move(self):
        bdir = os.path.join(self.extract_path, "boolector")
        for f in os.listdir(bdir):
            if f.startswith("boolector") and f.endswith(".so"):
                SolverInstaller.mv(os.path.join(bdir, f), self.bindings_dir)

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import boolector

                with open(os.path.join(self.extract_path, "boolector", "VERSION")) as f:
                    return f.read().strip()

            except ImportError:
                if "boolector" in sys.modules:
                    del sys.modules["boolector"]
                return None
            except IOError:
                return None

        return None
