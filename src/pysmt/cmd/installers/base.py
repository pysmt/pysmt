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
import importlib.metadata
import importlib.util
import os
import platform
import shutil
import site
import struct
import subprocess
import sys
import sysconfig
import tarfile
import urllib.request
import zipfile
from contextlib import contextmanager
from urllib.error import HTTPError, URLError

from pysmt.exceptions import PysmtException


@contextmanager
def TemporaryPath(path):
    """Context that substitutes the system path to test for API presence or absence"""
    old_path = list(sys.path)
    try:
        sys.path = path + sys.path
        yield
    finally:
        sys.path = old_path


class SolverInstaller:
    SOLVER: str | None = None

    def __init__(
        self,
        install_dir,
        target,
        solver_version,
        archive_name=None,
        native_link=None,
    ):
        self.target = target
        self.site_dir = site_dir(target)
        self.install_dir = install_dir
        self.solver_version = solver_version

        self.trials_404 = 3

        self.base_dir = os.path.join(self.install_dir, self.SOLVER)
        if not os.path.exists(self.base_dir):
            os.mkdir(self.base_dir)

        self.native_link = native_link
        self.archive_name = archive_name
        if self.archive_name is not None:
            self.archive_path = os.path.join(self.base_dir, self.archive_name)
            if self.archive_path.endswith(".tar.gz"):
                self.extract_path = self.archive_path[:-7]  # get rid of '.tar.gz'
            elif self.archive_path.endswith(".tar.bz2"):
                self.extract_path = self.archive_path[:-8]  # get rid of '.tar.bz2'
            elif self.archive_path.endswith(".zip"):
                self.extract_path = self.archive_path[:-4]  # get rid of '.zip'
            else:
                self.extract_path = None
        else:
            self.archive_path = None
            self.extract_path = None

    @property
    def os_name(self):
        return platform.system().lower()

    @property
    def architecture(self):
        if self.bits == 64:
            return "x86_64"
        else:
            return "x86"

    @property
    def bits(self):
        return 8 * struct.calcsize("P")

    @property
    def python_version(self):
        return f"{sys.version_info.major}.{sys.version_info.minor}"

    def download_links(self):
        if self.native_link is not None:
            yield self.native_link.format(
                archive_name=self.archive_name, solver_version=self.solver_version
            )

    def download(self):
        """Downloads the archive"""
        if self.archive_path and not os.path.exists(self.archive_path):
            for turn in range(self.trials_404):
                for link in self.download_links():
                    try:
                        return self.do_download(link, self.archive_path)
                    except HTTPError as e:
                        if e.code != 404:
                            raise
                        print(
                            "HTTP 404 while trying to get the archive using link"
                            f" '{link}' (trial {turn + 1}/{self.trials_404})"
                        )
                    except URLError as e:
                        print(
                            "Error while trying to get the archive using link"
                            f" '{link}' (trial {turn + 1}/{self.trials_404})"
                        )
                        raise e

    def unpack(self):
        """Unpacks the archive"""
        if self.archive_path:
            path = self.archive_path
            if path.endswith(".zip"):
                SolverInstaller.unzip(path, directory=self.base_dir)
            elif path.endswith(".tar.bz2"):
                SolverInstaller.untar(path, directory=self.base_dir, mode="r:bz2")
            elif path.endswith(".tar.gz"):
                SolverInstaller.untar(path, directory=self.base_dir)
            else:
                raise ValueError(f"Unsupported archive for extraction: {path}")

    def compile(self):
        """Performs the compilation if needed"""

    def move(self):
        """Moves relevant files in site_dir"""

    def install(self, force_redo=False):
        """Performs the installation of the solver"""
        if (not force_redo) and self.is_installed():
            return True

        if force_redo:
            SolverInstaller.clean_dir(self.base_dir)

        self.download()
        self.unpack()
        self.compile()
        self.move()
        return

    def is_installed(self):
        """Checks if the solver is installed and usable"""
        ver = self.get_installed_version()
        return (ver is not None) and (ver == self.solver_version)

    def get_installed_version(self):
        """Returns a string representing the version of the solver currently
        installed or None if the solver is not found"""
        return None

    @staticmethod
    def do_download(url, file_name):
        """Downloads the given url into the given file name"""
        u = urllib.request.urlopen(url)
        with open(file_name, "wb") as f:
            meta = u.info()
            if meta.get("Content-Length") and len(meta.get("Content-Length")) > 0:
                file_size = int(meta.get("Content-Length"))
                print(f"Downloading: {file_name} Bytes: {file_size}")

            block_sz = 8192
            count = 0
            while True:
                buff = u.read(block_sz)
                if not buff:
                    break

                f.write(buff)
                if (
                    meta.get("Content-Length")
                    and len(meta.get("Content-Length")) > 0
                    and sys.stdout.isatty()
                ):
                    count += len(buff)
                    perc = (float(count) / float(file_size)) * 100.0
                    str_perc = f"{perc:.1f}%"
                    sys.stdout.write("\r")
                    sys.stdout.write(str_perc)
                    sys.stdout.write(" " * (10 - len(str_perc)))

        print("")
        return True

    @staticmethod
    def run_python(script, directory=None, env_variables=None, get_output=False):
        """Executes a python script"""
        interpreter = "python"
        if sys.executable:
            interpreter = sys.executable

        if isinstance(script, str):
            script = script.split()
        cmd = [interpreter, *script]
        return SolverInstaller.run(
            cmd, directory=directory, env_variables=env_variables, get_output=get_output
        )

    @staticmethod
    def run(
        program,
        directory=None,
        env_variables=None,
        get_output=False,
        suppress_stderr=False,
    ):
        """Executes an arbitrary program"""
        environment = os.environ.copy()
        if env_variables is not None:
            for k, v in env_variables.items():
                environment[k] = v

        stderr = subprocess.DEVNULL if suppress_stderr else None
        if isinstance(program, str):
            program = program.split()
        if get_output:
            output = subprocess.check_output(
                program, env=environment, cwd=directory, stderr=stderr
            )
            return output.decode("ascii")
        else:
            subprocess.check_call(
                program, env=environment, cwd=directory, stderr=stderr
            )

    @staticmethod
    def replace_in_file(file_path, old_str, new_str):
        """Replaces all occurrences of old_str with new_str in the given file"""
        with open(file_path) as f:
            content = f.read()
        content = content.replace(old_str, new_str)
        with open(file_path, "w") as f:
            f.write(content)

    @staticmethod
    def clean_dir(path):
        """Empties a (possibly non-existent) directory"""
        if os.path.exists(path):
            shutil.rmtree(path)
        os.mkdir(path)

    @staticmethod
    def mv(source, dest):
        """Similarly to the UNIX mv command, moves / renames source_file in
        dest (if dest is a file name) otherwise moves source_file in
        the directory dest
        """
        if os.path.isdir(dest):
            dest = os.path.join(dest, os.path.basename(source))

        if os.path.isdir(source):
            if os.path.exists(dest):
                if os.path.isdir(dest):
                    shutil.rmtree(dest, ignore_errors=True)
                else:
                    os.unlink(dest)
            shutil.copytree(source, dest, symlinks=True)
            shutil.rmtree(source, ignore_errors=True)
        else:
            shutil.copy(source, dest)
            os.unlink(source)

    @staticmethod
    def untar(fname, directory, mode="r:gz"):
        """Extracts the tarfile using the specified mode in the given directory."""
        with tarfile.open(fname, mode) as tfile:
            tfile.extractall(directory)

    @staticmethod
    def unzip(fname, directory):
        """Unzips the given archive into the given directory"""
        myzip = zipfile.ZipFile(fname, "r")
        myzip.extractall(directory)
        myzip.close()

    def get_installed_version_script(self, package):
        check_version_script = os.path.abspath(
            os.path.join(os.path.dirname(__file__), "..", "check_version.py")
        )
        env = {}
        for k in ["LD_LIBRARY_PATH", "PATH", "PYTHONPATH"]:
            if k in os.environ:
                env[k] = self.site_dir + os.pathsep + os.environ[k]
            else:
                env[k] = self.site_dir

        try:
            output = self.run_python(
                [check_version_script, package], env_variables=env, get_output=True
            )
            output = output.strip()
        except Exception:
            print(f"Error while checking {package}")
            return None

        if output == "NOT INSTALLED":
            return None
        return output

    def find_python_config(self):
        command_tplate = "python%s-config"
        alternatives = [self.python_version, ""]
        command = None
        for alt in alternatives:
            name = command_tplate % alt
            command = shutil.which(name)
            if command is not None:
                break
        return command

    @staticmethod
    def run_setup_py(args, directory):
        """Runs a setup.py command, installing setuptools first if it is missing"""
        if importlib.util.find_spec("setuptools") is None:
            pip_install(["setuptools"])
        SolverInstaller.run_python(["setup.py", *args], directory=directory)


def site_dir(target=None):
    """Returns the directory where build-based installers place the bindings."""
    if target is not None:
        return target
    platlib = sysconfig.get_path("platlib")
    if os.access(platlib, os.W_OK):
        return platlib
    user_site = site.getusersitepackages()
    os.makedirs(user_site, exist_ok=True)
    return user_site


def pip_install_command(requirements, target=None, force=False):
    """Returns the command installing the requirements into the running interpreter."""
    if importlib.util.find_spec("pip") is not None:
        cmd = [sys.executable, "-m", "pip", "install"]
        reinstall = "--force-reinstall"
    elif shutil.which("uv") is not None:
        cmd = ["uv", "pip", "install", "--python", sys.executable]
        reinstall = "--reinstall"
    else:
        raise PysmtException(
            "pysmt-install needs pip or uv to install solvers. "
            "Install pip in this environment (python -m ensurepip) or install uv."
        )
    if target is not None:
        # pip replaces packages that already exist in the target dir only with --upgrade
        cmd += ["--target", target, "--upgrade"]
    if force:
        cmd.append(reinstall)
    return cmd + list(requirements)


def pip_install(requirements, target=None, force=False):
    """Installs the requirements into the running interpreter (or into target)."""
    cmd = pip_install_command(requirements, target=target, force=force)
    print(" ".join(cmd), flush=True)
    try:
        subprocess.check_call(cmd)
    except subprocess.CalledProcessError as e:
        marker = os.path.join(sysconfig.get_path("stdlib"), "EXTERNALLY-MANAGED")
        if target is None and os.path.exists(marker) and sys.prefix == sys.base_prefix:
            raise PysmtException(
                "This Python environment is externally managed (PEP 668). "
                "Run pysmt-install from a virtual environment or use --target DIR."
            ) from e
        raise


def installed_version(distribution, path=None):
    """Returns the version of the distribution found in path (default: sys.path)."""
    dists = importlib.metadata.distributions(name=distribution, path=path or sys.path)
    for dist in dists:
        return dist.version
    return None
