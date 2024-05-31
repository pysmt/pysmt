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


class CVC5Installer(SolverInstaller):

    SOLVER = "cvc5"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, git_tag='master'):
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 mirror_link=mirror_link)

    def move(self):
        pass

    def compile(self):
        print(self.bindings_dir)
        SolverInstaller.run_python("-m pip install --upgrade --target=%s cvc5==%s" % (self.bindings_dir, self.solver_version))

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "cvc5")
