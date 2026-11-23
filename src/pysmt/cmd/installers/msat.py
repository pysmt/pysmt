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

from pysmt.cmd.installers.base import SolverInstaller, installed_version, pip_install
from pysmt.exceptions import PysmtException

# Inserted before the setup() call of the bindings' setup.py (see patch_setup_py)
SETUP_PY_PREAMBLE = """\
from setuptools.command.build_ext import build_ext as _build_ext


class build_ext(_build_ext):
    def run(self):
        super().run()
        # pysmt: ship the solver's shared libraries (e.g., DLLs) next to the extension
        for d in ("bin", "lib"):
            libdir = os.path.join(MATHSAT_DIR, d)
            for f in os.listdir(libdir):
                if f.endswith((".dll", ".so", ".dylib")):
                    self.copy_file(os.path.join(libdir, f), self.build_lib)


setup(cmdclass={"build_ext": build_ext}, py_modules=[%r], name="""


class MathSATFamilyInstaller(SolverInstaller):
    """Installs the Python bindings shipped in a MathSAT or OptiMathSAT release."""

    # Name of the Python module, which is also the name of the distribution
    MODULE: str

    def __init__(self, **kwargs):
        SolverInstaller.__init__(self, **kwargs)
        self.python_bindings_dir = os.path.join(self.extract_path, "python")

    def compile(self):
        self.patch_setup_py()
        # We get here only if this version is missing or --force was given
        pip_install(
            [os.path.abspath(self.python_bindings_dir)], target=self.target, force=True
        )

    def patch_setup_py(self):
        """Makes the bindings' setup.py build a complete, versioned package."""
        path = os.path.join(self.python_bindings_dir, "setup.py")
        with open(path, "r") as f:
            content = f.read()
        mathsat_dir = os.path.abspath(self.extract_path)
        replacements = [
            # pip may build in a copy of the directory, where '..' is not the archive
            ("MATHSAT_DIR = '..'", "MATHSAT_DIR = %r" % mathsat_dir),
            # The version is what --check and pip report for the installed bindings
            ("version='0.1',", "version=%r," % self.solver_version),
            ("setup(name=", SETUP_PY_PREAMBLE % self.MODULE),
        ]
        if self.os_name == "linux":
            # Finds shared libraries placed next to the extension without LD_LIBRARY_PATH
            replacements.append(
                ("extra_link_args = []", "extra_link_args = ['-Wl,-rpath,$ORIGIN']")
            )
        for old, new in replacements:
            if content.count(old) != 1:
                raise PysmtException("Cannot patch %s: %r not found" % (path, old))
            content = content.replace(old, new)
        with open(path, "w") as f:
            f.write(content)

    def get_installed_version(self):
        # With --target, a copy in the running environment must not count
        path = None if self.target is None else [self.target]
        return installed_version(self.MODULE, path=path)


class MSatInstaller(MathSATFamilyInstaller):
    SOLVER = "msat"
    MODULE = "mathsat"

    def __init__(self, install_dir, target, solver_version, mirror_link=None):

        # Getting the right archive name
        archive_name_template = "mathsat-{version}-{os}-{arch}.{ext}"
        format = {
            "version": solver_version,
            "os": self.os_name,
            "arch": self.architecture,
            "ext": "tar.gz",
        }
        if self.os_name == "windows":
            archive_name_template = "mathsat-{version}-{os}.{ext}"
            format["ext"] = "zip"
            format["os"] = "win64"
        elif self.os_name == "darwin":
            # Since version 5.6.7 the architecture is not included in the
            # pkg name for the OSX release as it is considered a "univeral binary"
            archive_name_template = "mathsat-{version}-{os}.{ext}"
            format["os"] = "macos"

        archive_name = archive_name_template.format(**format)

        native_link = "https://mathsat.fbk.eu/release/{archive_name}"

        MathSATFamilyInstaller.__init__(
            self,
            install_dir=install_dir,
            target=target,
            solver_version=solver_version,
            archive_name=archive_name,
            native_link=native_link,
            mirror_link=mirror_link,
        )

    def compile(self):
        if self.os_name == "windows":
            libdir = os.path.join(self.python_bindings_dir, "../lib")
            incdir = os.path.join(self.python_bindings_dir, "../include")

            gmp_win_url = "https://github.com/apotocki/gmp-win/releases/download/6.3.0/gmp-6.3.0.zip"
            gmp_archive = os.path.join(self.base_dir, "gmp-6.3.0.zip")
            gmp_dir = os.path.join(self.base_dir, "gmp-6.3.0")
            SolverInstaller.clean_dir(gmp_dir)
            SolverInstaller.do_download(url=gmp_win_url, file_name=gmp_archive)
            SolverInstaller.unzip(gmp_archive, gmp_dir)

            gmp_include_dir = os.path.join(self.base_dir, "gmp-6.3.0", "include")
            gmp_lib_dir = os.path.join(self.base_dir, "gmp-6.3.0", "lib")
            SolverInstaller.mv(os.path.join(gmp_include_dir, "gmp.h"), incdir)
            SolverInstaller.mv(
                source=os.path.join(gmp_lib_dir, "gmpdll.lib"),
                dest=os.path.join(libdir, "gmp.lib"),
            )

            # The MathSAT setup.py expects to link against "mpir" on Windows,
            # but we link against "gmp", so we need to patch the setup.py
            setup_py_path = os.path.join(self.python_bindings_dir, "setup.py")
            SolverInstaller.replace_in_file(setup_py_path, "mpir", "gmp")

        MathSATFamilyInstaller.compile(self)
