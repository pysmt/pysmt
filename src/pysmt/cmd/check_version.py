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

import re
import sys


def check_version(module):
    try:
        if module in ("msat", "optimsat"):
            if module == "msat":
                import mathsat  # type: ignore[import]

                version_str = mathsat.msat_get_version()
            else:
                import optimathsat  # type: ignore[import]

                version_str = optimathsat.msat_get_version()
            m = re.match(r"^MathSAT5 version (\d+\.\d+\.\d+) .*$", version_str)
            if m is not None:
                version = m.group(1)
            else:
                m = re.match(r"^MathSAT5 version (\w+) .*$", version_str)
                if m is not None:
                    version = m.group(1)

        elif module == "picosat":
            import picosat  # type: ignore[import]

            version = picosat.picosat_version()

        elif module == "yices":
            import yices_api  # type: ignore[import]

            version = yices_api.yices_python_version
        else:
            print("Invalid argument '%s'" % module)
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
