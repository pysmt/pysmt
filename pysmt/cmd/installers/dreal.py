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
import sys

from pysmt.cmd.installers.base import SolverInstaller, TemporaryPath


class DRealInstaller(SolverInstaller):

    SOLVER = "dreal"

    def __init__(self, install_dir, bindings_dir, solver_version,
                 mirror_link=None, git_version='HEAD'):
        archive_name = "dreal3-%s.tar.gz" % git_version
        native_link = "https://codeload.github.com/pysmt/dreal3/tar.gz/%s" % (git_version)
        SolverInstaller.__init__(self, install_dir=install_dir,
                                 bindings_dir=bindings_dir,
                                 solver_version=solver_version,
                                 archive_name=archive_name,
                                 native_link=native_link,
                                 mirror_link=mirror_link)
        self.git_version = git_version
        self.bin_path = os.path.join(self.bindings_dir, "dreal_bin")

    def move(self):
        api_dir = os.path.join(self.extract_path, "src", "api")
        SolverInstaller.mv(os.path.join(api_dir, "drealpy.py"),
                           self.bindings_dir)

        libdir = "lib.%s-%s-%s" % (self.os_name, self.architecture,
                                   self.python_version)
        sodir = os.path.join(api_dir, "build", libdir)
        for f in os.listdir(sodir):
            if f.endswith(".so"):
                SolverInstaller.mv(os.path.join(sodir, f),
                                   os.path.join(self.bindings_dir, "_drealpy.so"))

    def get_dependencies(self):
        third_party_libs = os.path.join(self.extract_path, "src", "third_party")
        if not os.path.exists(third_party_libs):
            os.mkdir(third_party_libs)
        target = os.path.join(third_party_libs, "%s.zip")
        source = "https://github.com/dreal-deps/%s/archive/master.zip"
        dependencies = ["capdDynSys-4.0",
                        "clp-1.16",
                        "filibxx",
                        "Catch",
                        "ibex-lib",
                        "easyloggingpp",
                        "glpk",
                        "ezoptionparser",
                        "nlopt",
                        "json",
                        "picosat",
                        "adept",
                        ]
        for dep in dependencies:
            if os.path.exists(target % dep): continue
            print("Downloading %s ..." % dep)
            self.do_download(source % dep, target % dep)

    def compile(self):
        # Additional downloads
        self.get_dependencies()

        self.bin_path = os.path.join(self.bindings_dir, "dreal_bin")
        # Prepare the building system
        cmake_cmd = "cmake -DCMAKE_BUILD_TYPE=RELEASE " +\
                    "-DBUILD_SHARED_LIB=ON " +\
                    "-DUSE_LOCAL_THIRD_PARTY=ON " +\
                    "-DCMAKE_INSTALL_PREFIX=%s " % self.bin_path +\
                    "../src"

        # Do we need these?
        build_path = os.path.join(self.extract_path, "build")
        SolverInstaller.clean_dir(build_path)

        # Configure and build dReal
        SolverInstaller.run(cmake_cmd, directory=build_path)
        SolverInstaller.run("make", directory=build_path)

        SolverInstaller.run("make install", directory=build_path)
        # Build the Wrapper
        SolverInstaller.run_python("setup.py build_ext --dreal-dir=%s" % self.bin_path,
                                   directory=os.path.join(self.extract_path, "src", "api"))
        SolverInstaller.run_python("setup.py build --dreal-dir=%s" % self.bin_path,
                                   directory=os.path.join(self.extract_path, "src", "api"))

    def get_installed_version(self):
        with TemporaryPath([self.bindings_dir]):
            try:
                import drealpy
                full_version = drealpy.dreal_version()
                version = full_version.split(" ")[1]
                return version
            except ImportError:
                if "drealpy" in sys.modules:
                    del sys.modules["drealpy"]
                return None
