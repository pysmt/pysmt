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
        import glob
        # Build lingeling
        lingeling_archive = glob.glob(os.path.join(self.extract_path,
                                                   "archives", "lingeling-*.tar.gz"))[0]
        SolverInstaller.untar(lingeling_archive, self.extract_path)
        lingeling_dir = glob.glob(os.path.join(self.extract_path,
                                               "lingeling*"))[0]
        SolverInstaller.mv(lingeling_dir,
                           os.path.join(self.extract_path, "lingeling"))
        SolverInstaller.run("bash ./configure.sh -fPIC",
                          directory=os.path.join(self.extract_path, "lingeling"))
        SolverInstaller.run("make",
                          directory=os.path.join(self.extract_path, "lingeling"))

        # Build Btor
        boolector_archive = glob.glob(os.path.join(self.extract_path,
                                                   "archives", "boolector-*.tar.gz"))[0]
        SolverInstaller.untar(boolector_archive, self.extract_path)
        boolector_dir = glob.glob(os.path.join(self.extract_path,
                                               "boolector*"))[0]
        SolverInstaller.mv(boolector_dir,
                           os.path.join(self.extract_path, "boolector"))

        SolverInstaller.run("bash ./configure.sh -python",
                          directory=os.path.join(self.extract_path, "boolector"))
        SolverInstaller.run("make",
                          directory=os.path.join(self.extract_path, "boolector"))

        # Redo this step to make sure the correct version of python is used
        SolverInstaller.run_python("setup.py build_ext -b build -t build/api/python/tmp",
                                   directory=os.path.join(self.extract_path, "boolector"))


    def move(self):
        bdir = os.path.join(self.extract_path, "boolector/build")
        for f in os.listdir(bdir):
            if f.startswith("boolector") and f.endswith(".so"):
                SolverInstaller.mv(os.path.join(bdir, f), self.bindings_dir)

    def get_installed_version(self):
        res = self.get_installed_version_script(self.bindings_dir, "btor")
        version = None
        if res == "OK":
            vfile = os.path.join(self.extract_path, "boolector", "VERSION")
            try:
                with open(vfile) as f:
                    version = f.read().strip()
            except OSError:
                return None
        return version
