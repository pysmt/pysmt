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

from pysmt.exceptions import SolverAPINotFound


def check_version(module):
    try:
        if module == "picosat":
            import picosat  # type: ignore[import]

            version = picosat.picosat_version()

        elif module == "yices":
            # Loads libyices the way pySMT does, and reports the library version
            from pysmt.solvers.yices import yices_api

            version = yices_api.yices_version
        else:
            print("Invalid argument '%s'" % module)
            exit(-2)

    except (ImportError, SolverAPINotFound):
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
