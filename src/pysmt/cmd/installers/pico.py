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
import codecs
import glob
import json
import os
import urllib.request

from pysmt.cmd.installers.base import SolverInstaller


class PicoSATInstaller(SolverInstaller):
    SOLVER = "picosat"

    def __init__(
        self,
        install_dir,
        target,
        solver_version,
        pypicosat_minor_version,
    ):
        self.pypicosat_minor_version = pypicosat_minor_version
        self.complete_version = None
        SolverInstaller.__init__(
            self,
            install_dir=install_dir,
            target=target,
            solver_version=solver_version,
            native_link=None,
            archive_name=None,
        )

    def download(self):
        self.complete_version = "%s.%s" % (
            self.solver_version,
            self.pypicosat_minor_version,
        )
        pypi_link = (
            "https://pypi.python.org/pypi/pyPicoSAT/%s/json" % self.complete_version
        )
        response = urllib.request.urlopen(pypi_link)
        reader = codecs.getreader("utf-8")
        pypi_json = json.load(reader(response))

        self.native_link = pypi_json["urls"][0]["url"]
        self.archive_name = pypi_json["urls"][0]["filename"]
        self.archive_path = os.path.join(self.base_dir, self.archive_name)
        self.extract_path = os.path.join(self.base_dir, self.archive_name[:-7])

        SolverInstaller.download(self)

    def compile(self):
        picosat_dir = os.path.join(
            self.extract_path, "picosat-%s" % self.solver_version
        )
        SolverInstaller.run(
            "bash configure.sh",
            directory=picosat_dir,
            env_variables={"CFLAGS": " -fPIC"},
        )
        SolverInstaller.run(
            "make", directory=picosat_dir, env_variables={"CFLAGS": " -fPIC"}
        )
        SolverInstaller.run_setup_py(["build"], self.extract_path)

    def move(self):
        bdir = os.path.join(self.extract_path, "build")
        sodir = glob.glob(bdir + "/lib.*")[0]

        for f in os.listdir(sodir):
            if f.endswith(".so"):
                SolverInstaller.mv(os.path.join(sodir, f), self.site_dir)
        SolverInstaller.mv(os.path.join(self.extract_path, "picosat.py"), self.site_dir)

    def get_installed_version(self):
        return self.get_installed_version_script("picosat")
