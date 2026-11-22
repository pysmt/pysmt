import os
import tempfile

from pysmt.cmd.installers.base import SolverInstaller
from pysmt.test import TestCase, main


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


if __name__ == "__main__":
    main()
