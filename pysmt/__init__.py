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

VERSION = (0, 9, 6, "dev", 1)

# Try to provide human-readable version of latest commit for dev versions
# E.g. v0.5.1-4-g49a49f2-wip
#      * 4 commits after tag v0.5.1
#      * Latest commit "49a49f2"
#      * -wip: Working tree is dirty (non committed stuff)
# See: https://git-scm.com/docs/git-describe
if len(VERSION) == 5:
    import subprocess
    try:
        git_version = subprocess.check_output(["git", "describe",
                                               "--dirty=-wip"],
                                              stderr=subprocess.STDOUT)
        commits_from_tag = git_version.strip().decode('ascii')
        commits_from_tag = commits_from_tag.split("-")[1]
        commits_from_tag = int(commits_from_tag)
        VERSION = VERSION[:4] + (commits_from_tag,)
    except Exception as ex:
        pass

# PEP440 Format
__version__ = "%d.%d.%d.%s%d" % VERSION if len(VERSION) == 5 else \
              "%d.%d.%d" % VERSION
