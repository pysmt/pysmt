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
import re
import sys
import platform
import glob

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class MSatInstaller(SolverInstaller):

    SOLVER = "msat"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None):
        archive_name = "mathsat-%s-%s-%s.tar.gz" % (solver_version,
                                                    self.os_name,
                                                    self.architecture)
        if self.os_name == "darwin":
            archive_name = archive_name.replace("darwin", "darwin-libcxx")
        if self.os_name == "windows":
            archive_name = archive_name.replace("windows-x86_64", "win64")
            archive_name = archive_name.replace("windows-x86", "win32")
            archive_name = archive_name.replace(".tar.gz", "-msvc.zip")

        native_link = "http://mathsat.fbk.eu/download.php?file={archive_name}"

        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link = native_link,
                                 mirror_link=mirror_link)

        self.python_bindings_dir = os.path.join(self.extract_path, "python")

    def compile(self):
        if self.os_name == "windows":
            libdir = os.path.join(self.python_bindings_dir, "../lib")
            incdir = os.path.join(self.python_bindings_dir, "../include")
            deps_archive = os.path.join(self.base_dir, "deps.zip")
            SolverInstaller.do_download("https://github.com/mikand/tamer-windows-deps/archive/master.zip", deps_archive)
            SolverInstaller.unzip(deps_archive, self.base_dir)
            deps_dir = os.path.join(self.base_dir, "tamer-windows-deps-master")
            SolverInstaller.mv(os.path.join(deps_dir, "gmp/include/gmp.h"),
                               os.path.join(self.python_bindings_dir, "../include"))

            SolverInstaller.do_download("https://raw.githubusercontent.com/mikand/tamer-windows-deps/master/gmp/include/gmp.h", os.path.join(incdir, "gmp.h"))

            SolverInstaller.do_download("https://github.com/Legrandin/mpir-windows-builds/blob/master/mpir-2.6.0_VS2015_%s/mpir.dll?raw=true" % self.bits, os.path.join(libdir, "mpir.dll"))
            SolverInstaller.do_download("https://github.com/Legrandin/mpir-windows-builds/blob/master/mpir-2.6.0_VS2015_%s/mpir.lib?raw=true" % self.bits, os.path.join(libdir, "mpir.lib"))

            # Overwrite setup.py
            setup = """#!/usr/bin/env python

import os, sys
from setuptools import setup, Extension

extra_compile_args = []
extra_link_args = []

MATHSAT_DIR = '..'

libraries = ['mathsat', 'psapi', 'mpir']

setup(name='mathsat', version='0.1',
      description='MathSAT API',
      ext_modules=[Extension('_mathsat', ['mathsat_python_wrap.c'],
                             define_macros=[('SWIG','1')],
                             include_dirs=[os.path.join(MATHSAT_DIR,
                                                        'include')],
                             library_dirs=[os.path.join(MATHSAT_DIR, 'lib')],
                             extra_compile_args=extra_compile_args,
                             extra_link_args=extra_link_args,
                             libraries=libraries,
                             language='c++',
                             )]
      ) """
            with open(os.path.join(self.python_bindings_dir, "setup.py"), "w") as f:
                f.write(setup)
                f.write("\n")

            # Patching swig wrapper
            key = "if (arg2) msat_free(arg2);"
            subst = "if (arg2) free(arg2);"
            c_body = None
            with open(os.path.join(self.python_bindings_dir, "mathsat_python_wrap.c"), "r") as f:
                c_body = f.read()
            c_body = c_body.replace(key, subst)
            with open(os.path.join(self.python_bindings_dir, "mathsat_python_wrap.c"), "w") as f:
                f.write(c_body)

        SolverInstaller.run_python("./setup.py build", self.python_bindings_dir)
        if self.os_name == "windows":
            SolverInstaller.mv(os.path.join(libdir, "mathsat.dll"), self.bindings_dir)
            SolverInstaller.mv(os.path.join(libdir, "mpir.dll"), self.bindings_dir)

    def move(self):
        pdir = self.python_bindings_dir
        bdir = os.path.join(pdir, "build")
        sodir = glob.glob(bdir + "/lib.*")[0]

        for f in os.listdir(sodir):
            if f.endswith(".so") or f.endswith(".pyd"):
                SolverInstaller.mv(os.path.join(sodir, f), self.bindings_dir)
        SolverInstaller.mv(os.path.join(pdir, "mathsat.py"), self.bindings_dir)

    def get_installed_version(self):
        return self.get_installed_version_script(self.bindings_dir, "msat")
