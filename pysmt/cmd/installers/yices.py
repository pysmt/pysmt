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
import sys
import glob

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class YicesInstaller(SolverInstaller):

    SOLVER = "yices"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, yices_api_version=None):

        archive_name = "Yices-%s.tar.gz" % (solver_version)
        native_link = "https://github.com/SRI-CSL/yices2/archive/{archive_name}"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)

        self.yices_api_version = yices_api_version
        self.extract_path = os.path.join(self.base_dir, "yices2-Yices-%s" % self.solver_version)
        self.yices_path = os.path.join(self.base_dir, "yices_bin")

    def compile(self):
        # Prepare an empty folder for installing yices
        SolverInstaller.clean_dir(self.yices_path)

        SolverInstaller.run("autoconf", directory=self.extract_path)

        SolverInstaller.run("bash configure --prefix %s" % self.yices_path,
                            directory=self.extract_path)
        SolverInstaller.run("make", directory=self.extract_path)
        SolverInstaller.run("make install", directory=self.extract_path)

        if self.yices_api_version is None:
            SolverInstaller.run_python("-m pip install --upgrade --target=%s yices" % self.bindings_dir)
        else:
            SolverInstaller.run_python("-m pip install --upgrade --target=%s yices==%s" % (self.bindings_dir, self.yices_api_version))

        libdir = os.path.join(self.yices_path, "lib")
        yices_api_file = os.path.join(self.bindings_dir, "yices_api.py")
        with open(yices_api_file, 'r') as f:
            lines = f.readlines()
            if "sys.stderr.write" in lines[215]:
                lines.pop(215)
            if "else" in lines[226]:
                lines.insert(226, "    if _loadYicesFromPath('%s', libyicespath):\n        return\n" % libdir)
        with open(yices_api_file, 'w') as f:
            f.write("".join(lines))

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "yices")
