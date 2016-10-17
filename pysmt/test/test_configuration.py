#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
import os
from tempfile import NamedTemporaryFile

from pysmt.shortcuts import read_configuration, write_configuration
from pysmt.shortcuts import get_env
from pysmt.configuration import (configure_environment,
                                 write_environment_configuration)
from pysmt.environment import Environment
from pysmt.exceptions import PysmtIOError

from pysmt.test import TestCase, main
BASE_DIR = os.path.dirname(os.path.abspath(__file__))


class TestConfiguration(TestCase):

    def _get_config_path(self, config_name):
        return os.path.join(BASE_DIR, "configs", config_name)

    def _get_tmp_file(self):
        return NamedTemporaryFile(delete=False)

    def test_read(self):
        env = get_env()
        configure_environment(self._get_config_path("config1.ini"), env)
        self.assertTrue("mathsat-smt" in env.factory.all_solvers())
        self.assertTrue("z3-smt" in env.factory.all_solvers())

    def test_read_shortcut(self):
        read_configuration(self._get_config_path("config1.ini"))
        env = get_env()
        self.assertTrue("mathsat-smt" in env.factory.all_solvers())
        self.assertTrue("z3-smt" in env.factory.all_solvers())


    def test_write(self):
        env = get_env()
        configure_environment(self._get_config_path("config1.ini"), env)

        tmp = self._get_tmp_file()
        fname = tmp.name

        write_environment_configuration(fname, env)

        new_env = Environment()
        configure_environment(fname, new_env)
        try:
            os.remove(fname)
        except WindowsError:
            print("Error deleting file...")

        self.assertEqual(new_env.enable_infix_notation,
                          env.enable_infix_notation)
        self.assertEqual(new_env.factory.solver_preference_list,
                          env.factory.solver_preference_list)

        self.assertTrue("mathsat-smt" in new_env.factory.all_solvers())
        self.assertTrue("z3-smt" in new_env.factory.all_solvers())


    def test_write_shortcut(self):
        read_configuration(self._get_config_path("config1.ini"))

        tmp = self._get_tmp_file()
        fname = tmp.name

        write_configuration(fname)

        new_env = Environment()
        read_configuration(fname, new_env)
        try:
            os.remove(fname)
        except WindowsError:
            print("Error deleting file...")

        env = get_env()
        self.assertEqual(new_env.enable_infix_notation,
                          env.enable_infix_notation)
        self.assertEqual(new_env.factory.solver_preference_list,
                          env.factory.solver_preference_list)

        self.assertTrue("mathsat-smt" in new_env.factory.all_solvers())
        self.assertTrue("z3-smt" in new_env.factory.all_solvers())

    def test_nonexistent_conf(self):
        with self.assertRaises(PysmtIOError):
            read_configuration("/tmp/nonexistent")

    def test_bad_conf(self):
        with self.assertRaises(Exception):
            read_configuration(self._get_config_path("config_bad.ini"))


if __name__ == '__main__':
    main()
