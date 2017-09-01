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
from __future__ import absolute_import

import os
import sys

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class CVC4Installer(SolverInstaller):

    SOLVER = "cvc4"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, git_version='HEAD'):
        archive_name = "CVC4-%s.tar.gz" % git_version
        native_link = "https://codeload.github.com/CVC4/CVC4/tar.gz/%s" % (git_version)
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)
        self.git_version = git_version
        self.bin_path = os.path.join(self.bindings_dir, "CVC4_bin")

    def move(self):
        SolverInstaller.mv(os.path.join(self.bin_path, "share/pyshared/CVC4.py"),
                           self.bindings_dir)
        SolverInstaller.mv(os.path.join(self.bin_path, "lib/pyshared/_CVC4.so"),
                           self.bindings_dir)

    def compile(self):
        # Prepare the building system
        SolverInstaller.run("bash autogen.sh", directory=self.extract_path)

        # Build ANTLR
        SolverInstaller.run("bash get-antlr-3.4",
                            directory=os.path.join(self.extract_path, "contrib"))

        # Configure and build CVC4
        config_cmd = "./configure --prefix={bin_path} \
                                  --enable-language-bindings=python \
                                  --with-antlr-dir={dir_path}/antlr-3.4 ANTLR={dir_path}/antlr-3.4/bin/antlr3"
        config_cmd = config_cmd.format(bin_path=self.bin_path,
                                       dir_path=self.extract_path)

        if os.path.exists(sys.executable+"-config"):
            pyconfig = {"PYTHON_CONFIG": sys.executable+"-config"}
        else:
            pyconfig = {}

        SolverInstaller.run(config_cmd,  directory=self.extract_path,
                            env_variables=pyconfig)
        SolverInstaller.run("make", directory=self.extract_path,
                            env_variables=pyconfig)
        SolverInstaller.run("make install", directory=self.extract_path,
                            env_variables=pyconfig)


        # Fix the paths of the bindings
        SolverInstaller.mv(os.path.join(self.bin_path, "lib/pyshared/CVC4.so.4.0.0"),
                           os.path.join(self.bin_path, "lib/pyshared/_CVC4.so"))

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "cvc4")
