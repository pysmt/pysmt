import re
import sys
import os
import tarfile
import zipfile
import pip
import subprocess
import platform
import shutil

from contextlib import contextmanager

from six.moves import xrange
from six.moves.urllib import request as urllib2
from six.moves.urllib.error import HTTPError


def untar(fname, directory, mode='r:gz'):
    """Extracts the tarfile using the specified mode in the given directory."""
    tfile = tarfile.open(fname, mode)
    tfile.extractall(directory)


def unzip(fname, directory):
    """Unzips the given archive into the given directory"""
    myzip = zipfile.ZipFile(fname, "r")
    myzip.extractall(directory)
    myzip.close()


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
        return platform.machine()

    @property
    def python_version(self):
        return "%d.%d" % sys.version_info[0:2]

    def download_links(self):
        if self.mirror_link is not None:
            yield self.mirror_link.format(archive_name=self.archive_name)
        if self.native_link is not None:
            yield self.native_link.format(archive_name=self.archive_name)


    def download(self):
        """Downloads the archive from one of the mirrors"""
        if not os.path.exists(self.archive_path):
            for turn in xrange(self.trials_404):
                for i, link in enumerate(self.download_links()):
                    try:
                        return self.do_download(link, self.archive_path)
                    except HTTPError as e:
                        if e.code != 404:
                            raise
                        print("HTTP 404 while trying to get the archive using link" \
                              " #%d (trial %d/%d)" % (i, turn+1, self.trials_404))

    def unpack(self):
        """Unpacks the archive"""
        path = self.archive_path
        if path.endswith(".zip"):
            unzip(path, directory=self.base_dir)
        elif path.endswith(".tar.bz2"):
            untar(path, directory=self.base_dir, mode='r:bz2')
        elif path.endswith(".tar.gz"):
            untar(path, directory=self.base_dir)
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

        return self.is_installed()

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
        u = urllib2.urlopen(url)
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
    def run_python(script, directory=None, env_variables=None):
        """Executes a python script"""
        interpreter = 'python'
        if sys.executable:
            interpreter = sys.executable

        cmd = '{interpreter} {script}'.format(interpreter=interpreter,
                                              script=script)
        SolverInstaller.run(cmd, directory=directory, env_variables = env_variables)

    @staticmethod
    def run(program, directory=None, env_variables=None):
        """Executes an arbitrary program"""
        if directory is not None:
            cmd = 'cd {directory}; {program}'
        else:
            cmd = '{program}'

        if env_variables is not None:
            for k,v in env_variables.iteritems():
                cmd = "export %s='%s'; %s" % (k, v, cmd)

        os.system(cmd.format(directory=directory,
                             program=program))

    @staticmethod
    def clean_dir(path):
        """Empties a (possibly non-existent) directory"""
        if os.path.exists(path):
            shutil.rmtree(path)
        os.mkdir(path)

    @staticmethod
    def mv(source_file, dest):
        """Similarly to the UNIX mv command, moves / renames source_file in
        dest (if dest is a file name) otherwise moves source_file in
        the directory dest
        """
        if os.path.isdir(dest):
            fname = os.path.basename(source_file)
            dest_file = os.path.join(dest, fname)
        else:
            dest_file = dest

        if os.path.isfile(dest_file):
            os.unlink(dest_file)
        os.rename(source_file, dest_file)


class MSatInstaller(SolverInstaller):

    SOLVER = "msat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        archive_name = "mathsat-%s-%s-%s.tar.gz" % (solver_version,
                                                    self.os_name,
                                                    self.architecture)
        native_link = "http://mathsat.fbk.eu/download.php?file={archive_name}"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link = native_link,
                                 mirror_link=mirror_link)

        self.python_bindings_dir = os.path.join(self.extract_path, "python")


    def compile(self):
        SolverInstaller.run_python("./setup.py build", self.python_bindings_dir)


    def move(self):
        libdir = "lib.%s-%s-%s" % (self.os_name, self.architecture,
                                   self.python_version)
        pdir = self.python_bindings_dir
        bdir = os.path.join(pdir, "build")
        sodir = os.path.join(bdir, libdir)

        for f in os.listdir(sodir):
            if f.endswith(".so"):
                SolverInstaller.mv(os.path.join(sodir, f), self.bindings_dir)
        SolverInstaller.mv(os.path.join(pdir, "mathsat.py"), self.bindings_dir)


    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import mathsat
                version_str = mathsat.msat_get_version()
                m = re.match(r"^MathSAT5 version (\d+\.\d+\.\d+) .*$", version_str)
                if m is None:
                    return None
                return m.group(1)
            except ImportError:
                if "mathsat" in sys.modules:
                    del sys.modules["mathsat"]
                return None


class Z3Installer(SolverInstaller):

    SOLVER = "z3"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        arch = self.architecture
        if arch == "x86_64":
            arch = "x64"

        system = self.os_name
        if system == "linux":
            system = "ubuntu-14.04"

        archive_name = "z3-%s-%s-%s.zip" % (solver_version, arch, system)
        native_link = "https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/{archive_name}"

        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)


    def move(self):
        bpath = os.path.join(self.extract_path, "bin")
        files = ["libz3.so",
                 "z3consts.py",
                 "z3core.py",
                 "z3num.py",
                 "z3poly.py",
                 "z3printer.py",
                 "z3.py",
                 "z3rcf.py",
                 "z3test.py",
                 "z3types.py",
                 "z3util.py"]
        for f in files:
            SolverInstaller.mv(os.path.join(bpath, f), self.bindings_dir)

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import z3
                (major, minor, ver, _) = z3.get_version()
                return "%d.%d.%d" % (major, minor, ver)
            except ImportError:
                if "z3" in sys.modules:
                    del sys.modules["z3"]
                return None
        return None


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
        self.bin_path = os.path.join(self.base_dir, "CVC4_bin")

    def move(self):
        SolverInstaller.mv(os.path.join(self.bin_path, "share/pyshared/CVC4.py"),
                           self.bindings_dir)
        SolverInstaller.mv(os.path.join(self.bin_path, "lib/pyshared/_CVC4.so"),
                                        self.bindings_dir)

    def compile(self):
        # Patch the distribution to avoid a known problem
        patch_name = "cvc4_wrapper.patch"
        plink = "https://raw.githubusercontent.com/pysmt/solvers_patches/master/%s" % patch_name
        SolverInstaller.do_download(plink, os.path.join(self.extract_path, patch_name))

        # Apply patch
        SolverInstaller.run("patch -p1 -i %s" % patch_name,
                            directory=self.extract_path)

        # Prepare the building system
        SolverInstaller.run("bash autogen.sh", directory=self.extract_path)

        # Build ANTLR
        SolverInstaller.run("bash get-antlr-3.4",
                            directory=os.path.join(self.extract_path, "contrib"))

        # Configure and build CVC4
        config = "./configure --prefix={bin_path} \
                              --enable-language-bindings=python \
                              --with-antlr-dir={dir_path}/antlr-3.4 ANTLR={dir_path}/antlr-3.4/bin/antlr3;\
                  make; \
                  make install ".format(bin_path=self.bin_path, dir_path=self.extract_path)
        SolverInstaller.run(config, directory=self.extract_path)

        # Fix the paths of the bindings
        SolverInstaller.run("cp CVC4.so.3.0.0 _CVC4.so",
                            directory=os.path.join(self.bin_path, "lib/pyshared"))

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import CVC4
                return CVC4.Configuration_getVersionString()
            except ImportError:
                if "CVC4" in sys.modules:
                    del sys.modules["CVC4"]
                return None


class YicesInstaller(SolverInstaller):

    SOLVER = "yices"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        pack = "x86_64-unknown-linux-gnu-static-gmp"
        archive_name = "yices-%s-%s.tar.gz" % (solver_version, pack)
        native_link = "http://yices.csl.sri.com/cgi-bin/yices2-newnewdownload.cgi?file={archive_name}&accept=I+Agree"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)

        self.extract_path = os.path.join(self.base_dir, "yices-%s" % self.solver_version)
        self.yices_path = os.path.join(self.bindings_dir, "yices_bin")


    def install_pyices(self):
        pyices_git = "aa0b91c39aa00c19c2160e83aad822dc468ce328"
        pyices_base_name =  "pyices-%s" % pyices_git
        pyices_archive_name = "%s.tar.gz" % pyices_base_name
        pyices_archive = os.path.join(self.base_dir, pyices_archive_name)
        pyices_dir_path = os.path.join(self.base_dir, pyices_base_name)

        pyices_download_link = \
            "https://codeload.github.com/cheshire/pyices/tar.gz/%s" % pyices_git
        SolverInstaller.do_download(pyices_download_link, pyices_archive)

        SolverInstaller.clean_dir(pyices_dir_path)

        untar(pyices_archive, self.base_dir)
        # Build pyices
        SolverInstaller.run_python("setup.py install --prefix=%s" % self.install_dir,
                                   directory=pyices_dir_path,
                                   env_variables={"YICES_PATH" : self.yices_path})


    def compile(self):
        # Prepare an empty folder for installing yices
        SolverInstaller.clean_dir(self.yices_path)

        SolverInstaller.run("bash ./install-yices %s" % self.yices_path,
                            directory=self.extract_path)

        self.install_pyices()


    def move(self):
        sub = "lib/python%s/site-packages/pyices" % self.python_version
        SolverInstaller.mv(os.path.join(self.install_dir, sub),
                           self.bindings_dir)


    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import pyices
                import pyices.yices_lib as libyices
                import pyices.fix_env
                return libyices.yices_version
            except ImportError:
                if "pyices" in sys.modules:
                    del sys.modules["pyices"]
                return None


class PicoSATInstaller(SolverInstaller):

    SOLVER = "picosat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 mirror_link=mirror_link)

    def download(self):
        pass # Nothing to download

    def unpack(self):
        pass # Nothing to unpack

    def compile(self):
        pip.main(['install', '--target', self.bindings_dir, 'pypicosat'])

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import picosat
                return picosat.picosat_version()
            except ImportError:
                if "picosat" in sys.modules:
                    del sys.modules["picosat"]
                return None


class BtorInstaller(SolverInstaller):

    SOLVER = "btor"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        archive_name = "boolector-%s-with-lingeling-b85.tar.bz2" % solver_version
        native_link = "http://fmv.jku.at/boolector/{archive_name}"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 python_version=python_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)


    def compile(self):
        # First build
        SolverInstaller.run("make", directory=self.extract_path)

        # Reconfigure and build python bindings
        SolverInstaller.run("bash ./configure.sh -fPIC",
                          directory=os.path.join(self.extract_path, "lingeling"))
        SolverInstaller.run("make",
                          directory=os.path.join(self.extract_path, "lingeling"))

        SolverInstaller.run("bash ./configure -python",
                          directory=os.path.join(self.extract_path, "boolector"))
        SolverInstaller.run("make",
                          directory=os.path.join(self.extract_path, "boolector"))


    def move(self):
        bdir = os.path.join(self.extract_path, "boolector")
        for f in os.listdir(bdir):
            if f.startswith("boolector") and f.endswith(".so"):
                SolverInstaller.mv(os.path.join(bdir, f), self.bindings_dir)

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import boolector

                with open(os.path.join(self.extract_path, "boolector", "VERSION")) as f:
                    return f.read().strip()

            except ImportError:
                if "boolector" in sys.modules:
                    del sys.modules["boolector"]
                return None
            except IOError:
                return None

        return None


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
        command = ['python%s-config' % self.python_version, '--prefix']
        p = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=None)
        prefix = p.stdout.read()

        if not prefix or len(prefix) == 0:
            prefix = "/usr"

        SolverInstaller.run("make -C %s -f %s PYTHON_VER=python%s" \
                            " PYTHON_LOC=%s" % (self.extract_path, makefile,
                                                self.python_version, prefix))


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
