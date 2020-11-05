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
import multiprocessing

from pysmt.cmd.installers.base import SolverInstaller


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
        self.build_path = os.path.join(self.extract_path, "build")
        self.bin_path = os.path.join(self.build_path, "src", "bindings", "python")

    def move(self):
        CVC4_py = os.path.join(self.bin_path, "CVC4.py")
        CVC4_so = os.path.join(self.bin_path, "_CVC4.so")
        SolverInstaller.mv(CVC4_py, self.bindings_dir)
        SolverInstaller.mv(CVC4_so, self.bindings_dir)

    def compile(self):
        # Build ANTLR

        SolverInstaller.run("bash %s" % os.path.join("contrib", "get-antlr-3.4"),
                            directory=self.extract_path)

        # Build ABC
        # SolverInstaller.run("bash get-abc",
        #                     directory=os.path.join(self.extract_path, "contrib"))
        # Build GLPK
        # We could configure with --gpl --best, but this takes forever to build

        # Inject Python library and include paths into CMake because CVC4 search
        # system can be fooled in some systems
        import distutils.sysconfig as sysconfig
        PYTHON_LIBRARY = os.environ.get('PYSMT_PYTHON_LIBDIR')
        PYTHON_INCLUDE_DIR = sysconfig.get_python_inc()
        PYTHON_EXECUTABLE = sys.executable

        CMAKE_OPTS = '-DPYTHON_INCLUDE_DIR=' + PYTHON_INCLUDE_DIR
        CMAKE_OPTS += ' -DPYTHON_EXECUTABLE=' + PYTHON_EXECUTABLE
        if PYTHON_LIBRARY:
            CMAKE_OPTS += ' -DPYTHON_LIBRARY=' + PYTHON_LIBRARY

        SolverInstaller.run(['sed', '-i',
                             's|cmake_opts=""|cmake_opts="' + CMAKE_OPTS + '"|g',
                             './configure.sh'], directory=self.extract_path)

        # Configure and build CVC4
        config_cmd = "./configure.sh --language-bindings=python \
                                     --python%s" % self.python_version[0]

        if os.path.exists(sys.executable+"-config"):
            pyconfig = {"PYTHON_CONFIG": sys.executable+"-config"}
        else:
            pyconfig = {}

        SolverInstaller.run(config_cmd, directory=self.extract_path,
                            env_variables=pyconfig)
        SolverInstaller.run("make -j {}".format(multiprocessing.cpu_count()), directory=self.build_path,
                            env_variables=pyconfig)
        # SolverInstaller.run("make install", directory=self.build_path,
        #                     env_variables=pyconfig)

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "cvc4")
