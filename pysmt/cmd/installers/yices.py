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

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class YicesInstaller(SolverInstaller):

    SOLVER = "yices"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        pack = "x86_64-unknown-linux-gnu-static-gmp"
        archive_name = "yices-%s-%s.tar.gz" % (solver_version, pack)
        native_link = "http://yices.csl.sri.com/cgi-bin/yices2-newnewdownload.cgi?file={archive_name}&accept=I+Agree"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)

        self.extract_path = os.path.join(self.base_dir, "yices-%s" % self.solver_version)
        self.yices_path = os.path.join(self.bindings_dir, "yices_bin")


    def install_pyices(self):
        pyices_git = "aa0b91c39aa00c19c2160e83aad822dc468ce328"
        pyices_base_name =  "pyices-%s" % pyices_git
        pyices_archive_name = "%s.tar.gz" % pyices_base_name
        pyices_archive = os.path.join(self.base_dir, pyices_archive_name)
        pyices_dir_path = os.path.join(self.base_dir, pyices_base_name)

        pyices_download_link = \
            "https://codeload.github.com/cheshire/pyices/tar.gz/%s" % pyices_git
        SolverInstaller.do_download(pyices_download_link, pyices_archive)

        SolverInstaller.clean_dir(pyices_dir_path)

        SolverInstaller.untar(pyices_archive, self.base_dir)
        # Build pyices
        SolverInstaller.run_python("setup.py install --prefix=%s" % self.install_dir,
                                   directory=pyices_dir_path,
                                   env_variables={"YICES_PATH" : self.yices_path})


    def compile(self):
        # Prepare an empty folder for installing yices
        SolverInstaller.clean_dir(self.yices_path)

        SolverInstaller.run("bash ./install-yices %s" % self.yices_path,
                            directory=self.extract_path)

        self.install_pyices()


    def move(self):
        sub = "lib/python%s/site-packages/pyices" % self.python_version
        SolverInstaller.mv(os.path.join(self.install_dir, sub),
                           self.bindings_dir)


    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import pyices
                import pyices.yices_lib as libyices
                import pyices.fix_env
                return libyices.yices_version
            except ImportError:
                if "pyices" in sys.modules:
                    del sys.modules["pyices"]
                return None
