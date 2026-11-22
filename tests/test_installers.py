import os
import sys
import tempfile
from unittest import mock

from pysmt.cmd.installers import base
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


if __name__ == "__main__":
    main()
