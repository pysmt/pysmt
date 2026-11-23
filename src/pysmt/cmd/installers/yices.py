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
import glob
import os
import platform
import shutil

from pysmt.cmd.installers.base import SolverInstaller, pip_install


class YicesInstaller(SolverInstaller):
    """Installs SRI's yices Python API and copies libyices next to it.

    libyices comes from SRI's prebuilt release archive when one exists for
    this platform (see `binaries`), otherwise it is built from source.
    pysmt.solvers.yices loads the copy next to yices_api.py when no system
    libyices is found.
    """

    SOLVER = "yices"

    def __init__(
        self,
        install_dir,
        target,
        solver_version,
        mirror_link=None,
        yices_api_version=None,
        binaries=None,
    ):
        machine = (platform.system().lower(), platform.machine().lower())
        self.binary = (binaries or {}).get(machine)
        if self.binary is not None:
            archive_name = "yices-%s-%s-static-gmp.tar.gz" % (
                solver_version,
                self.binary,
            )
        else:
            archive_name = "yices-%s-src.tar.gz" % solver_version
        native_link = (
            "https://github.com/SRI-CSL/yices2/releases/download/"
            "yices-{solver_version}/{archive_name}"
        )
        SolverInstaller.__init__(
            self,
            install_dir=install_dir,
            target=target,
            solver_version=solver_version,
            archive_name=archive_name,
            native_link=native_link,
            mirror_link=mirror_link,
        )
        self.yices_api_version = yices_api_version
        # Both the binary and the source archives unpack into yices-<version>
        self.extract_path = os.path.join(self.base_dir, "yices-%s" % solver_version)

    def compile(self):
        libdir = os.path.join(self.extract_path, "lib")
        if self.binary is None:
            prefix = os.path.join(self.base_dir, "yices_bin")
            SolverInstaller.clean_dir(prefix)
            SolverInstaller.run(
                ["bash", "configure", "--prefix", prefix], directory=self.extract_path
            )
            SolverInstaller.run("make", directory=self.extract_path)
            SolverInstaller.run("make install", directory=self.extract_path)
            libdir = os.path.join(prefix, "lib")

        pip_install(
            ["yices==%s" % self.yices_api_version], target=self.target, force=True
        )

        # A stale libyices of another version would be found first
        for old in glob.glob(os.path.join(self.site_dir, "libyices*")):
            os.remove(old)
        for name in os.listdir(libdir):
            path = os.path.join(libdir, name)
            if (
                name.startswith("libyices")
                and not name.endswith(".a")
                and os.path.isfile(path)
                and not os.path.islink(path)
            ):
                shutil.copy(path, self.site_dir)

    def get_installed_version(self):
        # With --target, a copy in the running environment must not count
        if not os.path.exists(os.path.join(self.site_dir, "yices_api.py")):
            return None
        return self.get_installed_version_script("yices")
