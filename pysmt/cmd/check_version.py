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

import sys
import re


def check_version(module):
    try:
        if module == "z3":
            import z3
            (major, minor, ver, _) = z3.get_version()
            version = "%d.%d.%d" % (major, minor, ver)

        elif module == "msat":
            import mathsat
            version_str = mathsat.msat_get_version()
            m = re.match(r"^MathSAT5 version (\d+\.\d+\.\d+) .*$", version_str)
            if m is not None:
                version = m.group(1)

        elif module == "cudd":
            import repycudd
            doc = repycudd.DOCSTRING
            m = re.match(r"^PyCUDD (\d+\.\d+\.\d+).*", doc)
            if m is not None:
                version = m.group(1)

        elif module == "btor":
            import pyboolector
            version = "OK" # Just checking if import succeeds

        elif module == "cvc5":
            import cvc5
            solver = cvc5.Solver()
            version = solver.getVersion().decode('ascii')

        elif module == "cvc4":
            import CVC4
            version = CVC4.Configuration_getVersionString()

        elif module == "picosat":
            import picosat
            version = picosat.picosat_version()

        elif module == "yices":
            import yices_api
            version = yices_api.yices_python_version
        else:
            print("Invalid argument '%s'"  % module)
            exit(-2)

    except ImportError:
        version = None

    return version


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python %s <solver_name>" % sys.argv[0])
        exit(-1)

    module = sys.argv[1]
    version = check_version(module)

    if version is None:
        print("NOT INSTALLED")
    else:
        print(version)
