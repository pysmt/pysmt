import os
import sys
import tempfile
from unittest import mock

from pysmt.cmd.installers import MSatInstaller, base
from pysmt.cmd.installers.base import SolverInstaller, pip_install_command
from pysmt.exceptions import PysmtException
from tests import TestCase, main


class TestInstallers(TestCase):
    def test_run_python_path_with_space(self):
        with tempfile.TemporaryDirectory() as tmp:
            script = os.path.join(tmp, "with space", "echo.py")
            os.makedirs(os.path.dirname(script))
            with open(script, "w") as f:
                f.write("import sys; print(sys.argv[1])")
            arg = os.path.join(tmp, "another dir")
            out = SolverInstaller.run_python([script, arg], get_output=True)
            self.assertEqual(out.strip(), arg)

    def pip_command(self, has_pip, uv_path, **kwargs):
        spec = object() if has_pip else None
        with (
            mock.patch.object(base.importlib.util, "find_spec", return_value=spec),
            mock.patch.object(base.shutil, "which", return_value=uv_path),
        ):
            return pip_install_command(["z3-solver==1.0"], **kwargs)

    def test_pip_install_command_uses_pip(self):
        cmd = self.pip_command(True, "/bin/uv")
        self.assertEqual(
            cmd, [sys.executable, "-m", "pip", "install", "z3-solver==1.0"]
        )
        cmd = self.pip_command(True, None, target="/tmp/t", force=True)
        self.assertEqual(
            cmd[4:],
            ["--target", "/tmp/t", "--upgrade", "--force-reinstall", "z3-solver==1.0"],
        )

    def test_pip_install_command_falls_back_to_uv(self):
        cmd = self.pip_command(False, "/bin/uv", target="/tmp/t", force=True)
        self.assertEqual(
            cmd,
            ["uv", "pip", "install", "--python", sys.executable]
            + ["--target", "/tmp/t", "--upgrade", "--reinstall", "z3-solver==1.0"],
        )

    def test_pip_install_command_without_pip_or_uv(self):
        with self.assertRaises(PysmtException):
            self.pip_command(False, None)

    def msat_installer(self, tmp, setup_py):
        installer = MSatInstaller(
            install_dir=tmp, target=os.path.join(tmp, "t"), solver_version="5.6.20"
        )
        os.makedirs(installer.python_bindings_dir)
        with open(os.path.join(installer.python_bindings_dir, "setup.py"), "w") as f:
            f.write(setup_py)
        return installer

    def test_msat_patch_setup_py(self):
        with tempfile.TemporaryDirectory() as tmp:
            installer = self.msat_installer(tmp, MSAT_SETUP_PY)
            installer.patch_setup_py()
            setup_py = os.path.join(installer.python_bindings_dir, "setup.py")
            with open(setup_py) as f:
                content = f.read()
            compile(content, setup_py, "exec")
            self.assertIn("MATHSAT_DIR = %r" % installer.extract_path, content)
            self.assertIn("version='5.6.20'", content)
            self.assertIn("py_modules=['mathsat'], name='mathsat'", content)

    def test_msat_patch_setup_py_unknown_format(self):
        with tempfile.TemporaryDirectory() as tmp:
            installer = self.msat_installer(tmp, "from setuptools import setup\n")
            with self.assertRaises(PysmtException):
                installer.patch_setup_py()

    def test_msat_installed_version_in_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            installer = self.msat_installer(tmp, MSAT_SETUP_PY)
            self.assertIsNone(installer.get_installed_version())
            dist_info = os.path.join(tmp, "t", "mathsat-5.6.20.dist-info")
            os.makedirs(dist_info)
            with open(os.path.join(dist_info, "METADATA"), "w") as f:
                f.write("Metadata-Version: 2.1\nName: mathsat\nVersion: 5.6.20\n")
            self.assertEqual(installer.get_installed_version(), "5.6.20")


# The setup.py shipped in the python/ directory of the MathSAT 5.6.20 archives
MSAT_SETUP_PY = """\
import os, sys
from setuptools import setup, Extension

# adjust the following variables to customize your build
extra_compile_args = []
extra_link_args = []
extra_include_dirs = []
extra_library_dirs = []

MATHSAT_DIR = '..'

libraries = ['mathsat']
if sys.platform == 'win32':
    libraries += ['psapi', 'mpir']
else:
    libraries += ['gmpxx', 'gmp']

setup(name='mathsat',
      version='0.1',
      description='MathSAT API',
      ext_modules=[Extension('_mathsat', ['mathsat_python_wrap.c'],
                             define_macros=[('SWIG','1')],
                             include_dirs=[os.path.join(MATHSAT_DIR,
                                                        'include')] + \\
                             extra_include_dirs,
                             library_dirs=[os.path.join(MATHSAT_DIR, 'lib')] + \\
                             extra_library_dirs,
                             extra_compile_args=extra_compile_args,
                             extra_link_args=extra_link_args,
                             libraries=libraries,
                             language='c++',
                             )]
      )
"""


if __name__ == "__main__":
    main()
