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

def error():
    print("Invalid option try 'install' or 'shell'")
    exit(-1)

if __name__ == "__main__":
    import sys

    cmd = error
    if len(sys.argv) >= 2:
        sys.argv = sys.argv[1:]
        if sys.argv[0] == 'install':
            import pysmt.cmd.install
            cmd = pysmt.cmd.install.main
        elif sys.argv[0] == 'shell':
            import pysmt.cmd.shell
            cmd = pysmt.cmd.shell.main
    cmd()
