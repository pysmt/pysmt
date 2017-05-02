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

import sys
import subprocess
import pkgutil
import os.path

from pysmt.test import TestCase, main
import pysmt


class TestImports(TestCase):

    EXCLUSION_LIST = ["pysmt.test", "pysmt.solvers", "pysmt.cmd"]

    def test_imports(self):
        stack = [(pysmt.__name__, pysmt.__path__)]
        while stack:
            module_name, module_path = stack.pop()
            for _, name, ispkg in pkgutil.iter_modules(module_path):
                fullname = "%s.%s" % (module_name, name)
                command = [sys.executable, '-c', 'import %s' % fullname]
                returncode = subprocess.call(command)
                self.assertEqual(returncode, 0, msg="Failed to import %s module" % fullname)
                if ispkg and fullname not in TestImports.EXCLUSION_LIST:
                    stack.append((fullname, [os.path.join(p, name) for p in module_path]))

if __name__ == '__main__':
    main()
