import sys
import os
import subprocess
import re

from pysmt.cmd.installers.base import SolverInstaller
from pysmt.cmd.installers.utils import TemporaryPath


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
