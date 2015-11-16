import sys
import pip

from pysmt.cmd.installers.base import SolverInstaller
from pysmt.cmd.installers.utils import TemporaryPath

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
