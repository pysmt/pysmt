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


class BtorInstaller(SolverInstaller):

    SOLVER = "btor"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, git_version=None):
        native_link = "https://github.com/Boolector/boolector/archive/%s.tar.gz"
        archive_name = "boolector-%s.tar.gz"

        if git_version:
            native_link = native_link % git_version
            archive_name = archive_name % git_version
        else:
            native_link = native_link % solver_version
            archive_name = archive_name % solver_version

        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)

    def compile(self):
        # Override default Python library, include, and interpreter
        # path into Boolector's CMake because CMake can get confused
        # if multiple interpreters are available, especially python 2
        # vs python 3.
        import distutils.sysconfig as sysconfig
        import sys
        PYTHON_LIBRARY = os.environ.get('PYSMT_PYTHON_LIBDIR')
        PYTHON_INCLUDE_DIR = sysconfig.get_python_inc()
        PYTHON_EXECUTABLE = sys.executable
        CMAKE_OPTS = ' -DPYTHON_INCLUDE_DIR=' + PYTHON_INCLUDE_DIR
        CMAKE_OPTS += ' -DPYTHON_EXECUTABLE=' + PYTHON_EXECUTABLE
        if PYTHON_LIBRARY:
            CMAKE_OPTS += ' -DPYTHON_LIBRARY=' + PYTHON_LIBRARY

        # Unpack
        SolverInstaller.untar(os.path.join(self.base_dir, self.archive_name),
                              self.extract_path)

        # Build lingeling
        SolverInstaller.run("bash ./contrib/setup-lingeling.sh",
                            directory=self.extract_path)

        # Build Btor
        SolverInstaller.run("bash ./contrib/setup-btor2tools.sh",
                            directory=self.extract_path)


        # Build Boolector Solver
        SolverInstaller.run("bash ./configure.sh --python",
                            directory=self.extract_path,
                            env_variables={"CMAKE_OPTS": CMAKE_OPTS})

        SolverInstaller.run("make -j2",
                            directory=os.path.join(self.extract_path, "build"))

    def move(self):
        libdir = os.path.join(self.extract_path, "build", "lib")
        for f in os.listdir(libdir):
            if f.startswith("pyboolector") and f.endswith(".so"):
                SolverInstaller.mv(os.path.join(libdir, f),
                                   self.bindings_dir)


    def get_installed_version(self):
        import re

        res = self.get_installed_version_script(self.bindings_dir, "btor")
        version = None
        if res == "OK":
            vfile = os.path.join(self.extract_path, "CMakeLists.txt")
            try:
                with open(vfile) as f:
                    content = f.read().strip()
                    m = re.search('set\(VERSION "(.*)"\)', content)
                if m is not None:
                    version = m.group(1)
            except OSError:
                print("File not found")
                return None
            except IOError:
                print("IO Error")
                return None
        return version
