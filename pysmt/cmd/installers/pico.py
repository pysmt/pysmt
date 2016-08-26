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
import sys, os
import json
import codecs

from six.moves.urllib import request as urllib2

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class PicoSATInstaller(SolverInstaller):

    SOLVER = "picosat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 pypicosat_minor_version, mirror_link=None):

        self.complete_version = "%s.%s" % (solver_version, pypicosat_minor_version)
        pypi_link = "http://pypi.python.org/pypi/pyPicoSAT/%s/json" % self.complete_version
        response = urllib2.urlopen(pypi_link)
        reader = codecs.getreader("utf-8")
        pypi_json = json.load(reader(response))

        pypicosat_download_link = pypi_json["urls"][0]["url"]
        archive_name = pypi_json["urls"][0]["filename"]
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 mirror_link=mirror_link,
                                 native_link=pypicosat_download_link,
                                 archive_name=archive_name)
        self.extract_path = os.path.join(self.base_dir, archive_name[:-7])

    def compile(self):
        picosat_dir = os.path.join(self.extract_path, "picosat-%s" % self.solver_version)
        SolverInstaller.run('bash configure', directory=picosat_dir,
                            env_variables={"CFLAGS": " -fPIC"})
        SolverInstaller.run('make', directory=picosat_dir,
                            env_variables={"CFLAGS": " -fPIC"})
        SolverInstaller.run_python("setup.py build", directory=self.extract_path)

    def move(self):
        libdir = "lib.%s-%s-%s" % (self.os_name, self.architecture,
                                   self.python_version)
        bdir = os.path.join(self.extract_path, "build")
        sodir = os.path.join(bdir, libdir)

        for f in os.listdir(sodir):
            if f.endswith(".so"):
                SolverInstaller.mv(os.path.join(sodir, f), self.bindings_dir)
        SolverInstaller.mv(os.path.join(self.extract_path, "picosat.py"), self.bindings_dir)

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            version = None
            try:
                import picosat
                version = picosat.picosat_version()
            finally:
                if "picosat" in sys.modules:
                    del sys.modules["picosat"]
                # Return None, without raising an exception
                # pylint: disable=lost-exception
                return version
