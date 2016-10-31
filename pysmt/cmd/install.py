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

from six.moves import input

import os
import argparse
import sys

from collections import namedtuple

from pysmt.cmd.installers import MSatInstaller, Z3Installer, PicoSATInstaller
from pysmt.cmd.installers import CVC4Installer, YicesInstaller, BtorInstaller
from pysmt.cmd.installers import CuddInstaller, DRealInstaller

from pysmt.environment import get_env
from pysmt.exceptions import PysmtException
from pysmt import git_version

# Build a list of installers, one for each solver
Installer = namedtuple("Installer", ["InstallerClass", "version", "extra_params"])
INSTALLERS = [Installer(MSatInstaller,    "5.3.13", {}),
              Installer(Z3Installer,      "4.4.1", {"osx": "10.11"}),
              Installer(CVC4Installer,    "1.5-prerelease", {"git_version" : "c15ff43597b41ea457befecb1b0e2402e28cb523"}),
              Installer(YicesInstaller,   "2.5.1", {"yicespy_version": "07439670a54d08a76cfb931194e1eaf07ea026a1"}),
              Installer(BtorInstaller,    "2.2.0", {"lingeling_version": "bal"}),
              Installer(PicoSATInstaller, "960", {"pypicosat_minor_version" : "1610040816"}),
              Installer(CuddInstaller,    "2.0.3", {"git_version" : "75fe055c2a736a3ac3e971c1ade108b815edc96c"}),
              Installer(DRealInstaller,   "3.16.08", {"git_version" : "21b710a798a10a57049a4125f5ab25c58fefcfbb"}),
]


def get_requested_solvers():
    """Parses the PYSMT_SOLVER env variable to extract requirements to fulfill"""

    requested_solvers_str = os.environ.get("PYSMT_SOLVER")
    requested_solvers = []
    if requested_solvers_str is not None:
        keys = requested_solvers_str.split(",")
        requested_solvers = [x.lower().strip() for x in keys]
        if "all" in requested_solvers:
            requested_solvers = [x.InstallerClass.SOLVER for x in INSTALLERS]
    return requested_solvers


def check_installed(required_solvers, install_dir, bindings_dir, mirror_link):
    """Checks which solvers are visible to pySMT."""

    global_solvers_status = []
    print("Installed Solvers:")
    for i in INSTALLERS:
        installer_ = i.InstallerClass(install_dir=install_dir,
                                      bindings_dir=bindings_dir,
                                      solver_version=i.version,
                                      mirror_link=mirror_link,
                                      **i.extra_params)
        solver = installer_.SOLVER
        version = installer_.get_installed_version()
        is_installed = (version is not None)
        global_solvers_status.append((solver, is_installed, version))
        del installer_

    # Check which solvers are accessible from the Factory
    pypath_solvers = get_env().factory.all_solvers()
    for solver in required_solvers:
        if solver not in pypath_solvers:
            raise PysmtException("Was expecting to find %s installed" % solver)

    #
    # Output information
    #
    for (solver, is_installed, version) in global_solvers_status:
        msg = "  %s%s " % (solver.ljust(10), is_installed)
        msg += ("(%s)" % version).ljust(20)
        if solver not in pypath_solvers:
            msg += "Not in Python's path!"
        print(msg)
    print("")


    print("Solvers: %s" % ", ".join(name for name in pypath_solvers))
    qes = get_env().factory.all_quantifier_eliminators()
    print("Quantifier Eliminators: %s" % ", ".join(name for name in qes))

    ucs = get_env().factory.all_unsat_core_solvers()
    print("UNSAT-Cores: %s" % ", ".join(name for name in ucs))

    interps = get_env().factory.all_interpolators()
    print("Interpolators: %s" % ", ".join(name for name in interps))



def parse_options():
    parser = argparse.ArgumentParser(description='Install SMT Solvers.\n\n'
                                     'This script installs the solvers specified'
                                     ' on the command line or in the environment'
                                     ' variable PYSMT_SOLVER if not already '
                                     'instaled on the system.')
    parser.add_argument('--version', action='version',
                        version='%(prog)s {version}'.format(version=git_version()))

    for i in INSTALLERS:
        name = i.InstallerClass.SOLVER
        parser.add_argument('--%s' % name, dest=name, action='store_true',
                            default=False, help='Install %s' % name)

    parser.add_argument('--all', dest='all_solvers', action='store_true',
                        default=False,
                        help='Install all the solvers')

    parser.add_argument('--force', dest='force_redo', action='store_true',
                        default=False,
                        help='Forcedly rebuild the solvers even if already found')

    parser.add_argument('--check', dest='check', action='store_true',
                        default=False,
                        help='Checks the installation of the solvers')

    parser.add_argument('--env', dest='env', action='store_true',
                        default=False,
                        help='Prints a bash export command to extend the PYTHONPATH')

    parser.add_argument('--confirm-agreement', dest='skip_intro',
                        action='store_true', default=False,
                        help='Confirm that you agree with the licenses of the\
                        solvers and skip the interactive question')

    parser.add_argument('--install-path', dest='install_path',
                        type=str, default="~/.smt_solvers",
                        help='The folder to use for the installation')

    py_bindings = "~/.smt_solvers/python-bindings-%d.%d" % sys.version_info[0:2]
    parser.add_argument('--bindings-path', dest='bindings_path',
                        type=str, default=py_bindings,
                        help='The folder to use for the bindings')

    options = parser.parse_args()
    return options


################################################################################
# Main functions

def print_welcome():
    msg = """\
This script allows you to install the solvers supported by pySMT.

By executing this script, you confirm that you have read and agreed
with the licenses of each solver.

Notice: the installation process might require building tools
        (e.g., make and gcc).
"""
    print(msg)
    res = input("Continue? [Y]es/[N]o: ").lower()

    if res != "y":
        exit(-1)


def main():
    options = parse_options()

    # Address of a mirror website containing packages to avoid continuous
    # downloads from original websites in CI
    mirror_url = os.environ.get('PYSMT_INSTALL_MIRROR')
    if mirror_url is not None:
        mirror_url += "/{archive_name}"

    # This should work on any platform
    install_dir= os.path.expanduser(options.install_path)
    if not os.path.exists(install_dir):
        os.mkdir(install_dir)

    # This should work on any platform
    bindings_dir= os.path.expanduser(options.bindings_path)
    if not os.path.exists(bindings_dir):
        os.mkdir(bindings_dir)

    solvers_to_install = []
    all_solvers = options.all_solvers
    for i in INSTALLERS:
        name = i.InstallerClass.SOLVER
        if all_solvers or getattr(options, name):
            solvers_to_install.append(i)

    # Env variable controlling the solvers to be installed or checked
    requested_solvers = get_requested_solvers()
    if len(solvers_to_install) != 0 and len(requested_solvers) != 0:
        print("Warning: Solvers specified on the command line, "
              "ignoring env variable 'PYSMT_SOLVER'")
    if len(solvers_to_install) == 0:
        # No solver requested from cmd-line, checking ENV
        for i in INSTALLERS:
            name = i.InstallerClass.SOLVER
            if name in requested_solvers:
                solvers_to_install.append(i)

    if options.check:
        check_installed([x.InstallerClass.SOLVER for x in solvers_to_install],
                        install_dir=install_dir,
                        bindings_dir=bindings_dir,
                        mirror_link=mirror_url)
        exit(0)

    elif options.env:
        bindings_dir= os.path.expanduser(options.bindings_path)
        print("export PYTHONPATH=\""+ bindings_dir + ":${PYTHONPATH}\"")

    else:
        if len(solvers_to_install) == 0:
            print("Nothing to do.\nTry with '%s --help'" % sys.argv[0])
            exit(0)

        # Do the actual install
        if not options.skip_intro:
            print_welcome()

        for i in solvers_to_install:
            installer = i.InstallerClass(install_dir=install_dir,
                                         bindings_dir=bindings_dir,
                                         solver_version=i.version,
                                         mirror_link=mirror_url,
                                         **i.extra_params)
            installer.install(force_redo=options.force_redo)


if __name__ == "__main__":
    main()
