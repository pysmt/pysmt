import sys
import os

from pysmt.cmd.installers.base import SolverInstaller
from pysmt.cmd.installers.utils import TemporaryPath

class BtorInstaller(SolverInstaller):

    SOLVER = "btor"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        archive_name = "boolector-%s-with-lingeling-b85.tar.bz2" % solver_version
        native_link = "http://fmv.jku.at/boolector/{archive_name}"
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
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
