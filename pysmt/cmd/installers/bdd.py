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
import subprocess
import re

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath
from six import PY2


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

        # Build the pycudd
        command = ['python%s-config' % self.python_version, '--includes']
        p = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=None)
        prefix = p.stdout.read()
        if PY2:
            pass # Prefix is already a string
        else:
            # > PY3 Prefix is binary data
            prefix = prefix.decode()

        if not prefix or len(prefix) == 0:
            prefix = "/usr"

        SolverInstaller.run("make -C %s -f %s PYTHON_INCL=%s" %
                            (self.extract_path, makefile, prefix))


    def move(self):
        SolverInstaller.mv(os.path.join(self.extract_path, "repycudd.py"),
                           self.bindings_dir)
        SolverInstaller.mv(os.path.join(self.extract_path, "_repycudd.so"),
                           self.bindings_dir)


    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import repycudd
                doc = repycudd.DOCSTRING
                m = re.match(r"^PyCUDD (\d+\.\d+\.\d+).*", doc)
                if m is None:
                    return None
                return m.group(1)
            except ImportError:
                if "repycudd" in sys.modules:
                    del sys.modules["repycudd"]
                return None
        return None
