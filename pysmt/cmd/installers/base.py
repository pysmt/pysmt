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
import platform
import sys
import shutil
import zipfile
import tarfile
import struct
import subprocess
import urllib.request

from contextlib import contextmanager
from distutils import spawn
from distutils.dist import Distribution

from urllib.error import HTTPError, URLError


@contextmanager
def TemporaryPath(path):
    """Context that substitutes the system path to test for API presence or absence"""
    old_path = list(sys.path)
    try:
        sys.path = path + sys.path
        yield
    finally:
        sys.path = old_path


class SolverInstaller(object):

    SOLVER = None

    def __init__(self, install_dir, bindings_dir, solver_version,
                 archive_name=None, native_link=None, mirror_link=None):
        self.bindings_dir = bindings_dir
        self.install_dir = install_dir
        self.solver_version = solver_version
        self.mirror_link = mirror_link

        self.trials_404 = 3

        self.base_dir = os.path.join(self.install_dir, self.SOLVER)
        if not os.path.exists(self.base_dir):
            os.mkdir(self.base_dir)

        self.native_link = native_link
        self.archive_name = archive_name
        if self.archive_name is not None:
            self.archive_path = os.path.join(self.base_dir, self.archive_name)
            if self.archive_path.endswith(".tar.gz"):
                self.extract_path = self.archive_path[:-7] # get rid of '.tar.gz'
            elif self.archive_path.endswith(".tar.bz2"):
                self.extract_path = self.archive_path[:-8] # get rid of '.tar.bz2'
            elif self.archive_path.endswith(".zip"):
                self.extract_path = self.archive_path[:-4] # get rid of '.zip'
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
        return "%d.%d" % sys.version_info[0:2]

    def download_links(self):
        if self.mirror_link is not None:
            yield self.mirror_link.format(archive_name=self.archive_name, solver_version=self.solver_version)
        if self.native_link is not None:
            yield self.native_link.format(archive_name=self.archive_name, solver_version=self.solver_version)

    def download(self):
        """Downloads the archive from one of the mirrors"""
        if not os.path.exists(self.archive_path):
            for turn in range(self.trials_404):
                for i, link in enumerate(self.download_links()):
                    try:
                        return self.do_download(link, self.archive_path)
                    except HTTPError as e:
                        if e.code != 404:
                            raise
                        print("HTTP 404 while trying to get the archive using link" \
                              " '%s' (trial %d/%d)" % (link, turn+1, self.trials_404))
                    except URLError as e:
                        print("Error while trying to get the archive using link" \
                              " '%s' (trial %d/%d)" % (link, turn+1, self.trials_404))
                        raise e

    def unpack(self):
        """Unpacks the archive"""
        path = self.archive_path
        if path.endswith(".zip"):
            SolverInstaller.unzip(path, directory=self.base_dir)
        elif path.endswith(".tar.bz2"):
            SolverInstaller.untar(path, directory=self.base_dir, mode='r:bz2')
        elif path.endswith(".tar.gz"):
            SolverInstaller.untar(path, directory=self.base_dir)
        else:
            raise ValueError("Unsupported archive for extraction: %s" % path)

    def compile(self):
        """Performs the compilation if needed"""
        pass

    def move(self):
        """Moves relevant files in bindings_dir"""
        pass

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
        f = open(file_name, 'wb')
        meta = u.info()
        if meta.get("Content-Length") and len(meta.get("Content-Length")) > 0:
            file_size = int(meta.get("Content-Length"))
            print("Downloading: %s Bytes: %s" % (file_name, file_size))

        block_sz = 8192
        count = 0
        while True:
            buff = u.read(block_sz)
            if not buff:
                break

            f.write(buff)
            if meta.get("Content-Length") and len(meta.get("Content-Length")) > 0 \
               and sys.stdout.isatty():
                count += len(buff)
                perc = (float(count) / float(file_size)) * 100.0
                str_perc = "%.1f%%" % perc
                sys.stdout.write('\r')
                sys.stdout.write(str_perc)
                sys.stdout.write(" " * (10 - len(str_perc)))

        print("")
        f.close()
        return True

    @staticmethod
    def run_python(script, directory=None, env_variables=None, get_output=False):
        """Executes a python script"""
        interpreter = 'python'
        if sys.executable:
            interpreter = sys.executable

        cmd = '{interpreter} {script}'.format(interpreter=interpreter,
                                              script=script)
        return SolverInstaller.run(cmd, directory=directory,
                                   env_variables=env_variables,
                                   get_output=get_output)

    @staticmethod
    def run(program, directory=None, env_variables=None, get_output=False,
            suppress_stderr=False):
        """Executes an arbitrary program"""
        environment = os.environ.copy()
        if env_variables is not None:
            for k,v in env_variables.items():
                environment[k] = v

        stderr = None
        if suppress_stderr:
            stderr = open(os.devnull, 'w')
        if isinstance(program, str):
            program = program.split()
        if get_output:
            output = subprocess.check_output(program,
                                             env=environment,
                                             cwd=directory,
                                             stderr=stderr)
            if suppress_stderr:
                stderr.close()
            return output.decode("ascii")
        else:
            subprocess.check_call(program, env=environment,
                                  cwd=directory, stderr=stderr)
            if suppress_stderr:
                stderr.close()


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
    def untar(fname, directory, mode='r:gz'):
        """Extracts the tarfile using the specified mode in the given directory."""
        tfile = tarfile.open(fname, mode)
        tfile.extractall(directory)

    @staticmethod
    def unzip(fname, directory):
        """Unzips the given archive into the given directory"""
        myzip = zipfile.ZipFile(fname, "r")
        myzip.extractall(directory)
        myzip.close()

    def get_installed_version_script(self, bindings_dir, package):
        check_version_script = os.path.abspath(os.path.join(
                                 os.path.dirname(__file__),
                                 "..",
                                 "check_version.py"))
        env = {}
        for k in ["LD_LIBRARY_PATH", "PATH", "PYTHONPATH"]:
            if k in os.environ:
                env[k] = bindings_dir + os.pathsep + os.environ[k]
            else:
                env[k] = bindings_dir

        try:
            output = self.run_python("%s %s" % (check_version_script, package),
                                     env_variables=env,
                                     get_output=True)
            output = output.strip()
        except Exception as ex:
            print("Error while checking %s" % package)
            return None

        if output == "NOT INSTALLED":
            return None
        return output


    def find_python_config(self):
        command_tplate = 'python%s-config'
        alternatives = [self.python_version, '']
        command = None
        for alt in alternatives:
            name = command_tplate % alt
            command = spawn.find_executable(name)
            if command is not None:
                break
        return command


def package_install_site(name='', user=False, plat_specific=False):
    """pip-inspired, distutils-based method for fetching the
    default install location (site-packages path).

    Returns virtual environment or system site-packages, unless
    `user=True` in which case returns user-site (typ. under `~/.local/
    on linux).

    If there's a distinction (on a particular system) between platform
    specific and pure python package locations, set `plat_specific=True`
    to retrieve the former.
    """

    dist = Distribution({'name': name})
    dist.parse_config_files()
    inst = dist.get_command_obj('install', create=True)
    # NOTE: specifying user=True will create user-site
    if user:
        inst.user = user
        inst.prefix = ""
    inst.finalize_options()

    # platform-specific site vs. purelib (platform-independent) site
    if plat_specific:
        loc = inst.install_platlib
    else:
        loc = inst.install_purelib

    # install_lib specified in setup.cfg has highest precedence
    if 'install_lib' in dist.get_option_dict('install'):
        loc = inst.install_lib

    return loc


def running_under_virtualenv():
    """
    Return True if we're running inside a virtualenv, False otherwise.

    Note: copied from pip.
    """

    if hasattr(sys, 'real_prefix'):
        return True
    elif sys.prefix != getattr(sys, "base_prefix", sys.prefix):
        return True

    return False


def solver_install_site(plat_specific=False):
    """Determine solver's install site similarly to pip behaviour on Debian."""

    # install to local user-site, unless in virtualenv or running as root
    default_user = True
    if running_under_virtualenv():
        default_user = False
    try:
        if os.geteuid() == 0:
            default_user = False
    except:
        # getuid/geteuid not supported on windows
        pass

    return package_install_site(user=default_user, plat_specific=plat_specific)
