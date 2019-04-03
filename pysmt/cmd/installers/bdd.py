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


class CuddInstaller(SolverInstaller):

    SOLVER = "bdd"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, git_version='HEAD'):
        archive_name = "repycudd-%s.tar.gz" % git_version
        native_link = "https://codeload.github.com/pysmt/repycudd/tar.gz/%s" % git_version
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)
        self.git_version = git_version


    def compile(self):
        # Select the correct Makefile to be used
        makefile = "Makefile"
        if self.architecture == "x86_64":
            makefile = "Makefile_64bit"

        import distutils.sysconfig as sysconfig
        PYTHON_INCLUDE_DIR = sysconfig.get_python_inc()
        SolverInstaller.run("make -C %s -f %s PYTHON_INCL=-I%s" %
                            (self.extract_path, makefile, PYTHON_INCLUDE_DIR))


    def move(self):
        SolverInstaller.mv(os.path.join(self.extract_path, "repycudd.py"),
                           self.bindings_dir)
        SolverInstaller.mv(os.path.join(self.extract_path, "_repycudd.so"),
                           self.bindings_dir)


    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "cudd")
