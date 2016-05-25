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

from six.moves.urllib import request as urllib2
from six.moves import input, xrange

import os
import argparse
import sys

from collections import namedtuple

from pysmt.cmd.installers import MSatInstaller, Z3Installer, PicoSATInstaller
from pysmt.cmd.installers import CVC4Installer, YicesInstaller, BtorInstaller
from pysmt.cmd.installers import CuddInstaller


# Build a list of installers, one for each solver
Installer = namedtuple("Installer", ["InstallerClass", "version", "extra_params"])
INSTALLERS = [Installer(MSatInstaller,    "5.3.9", {}),
              Installer(Z3Installer,      "4.4.1", {}),
              Installer(CVC4Installer,    "1.5-prerelease", {"git_version" : "c15ff43597b41ea457befecb1b0e2402e28cb523"}),
              Installer(YicesInstaller,   "2.4.1", {}),
              Installer(BtorInstaller,    "2.2.0", {"lingeling_version": "bal"}),
              Installer(PicoSATInstaller, "960", {}),
              Installer(CuddInstaller,    "2.0.3", {"git_version" : "75fe055c2a736a3ac3e971c1ade108b815edc96c"})]

# The keys for the Solver(name=key) in pySMT
PYSMT_SOLVER_NAMES = ['msat', 'z3', 'cvc4', 'yices', 'bdd', 'picosat', 'btor']

# The keys for the QuantifierEliminator(name=key) in pySMT
PYSMT_QE_NAMES = ['msat_fm', 'msat_lw', 'z3', 'bdd']



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


def check_installed(required_solvers):
    """Checks which solvers are visible to pySMT."""

    from pysmt.shortcuts import Solver, QuantifierEliminator
    from pysmt.exceptions import NoSolverAvailableError

    print("Solvers:")
    for solver in PYSMT_SOLVER_NAMES:
        is_installed = False
        try:
            Solver(name=solver)
            is_installed = True
        except NoSolverAvailableError:
            is_installed = False
        print("  %s%s" % (solver.ljust(10), is_installed))

        if solver in required_solvers and not is_installed:
            raise Exception("Was expecting to find %s installed" % solver)

    print("\nQuantifier Eliminators:")
    for solver in PYSMT_QE_NAMES:
        is_installed = False
        try:
            QuantifierEliminator(name=solver)
            is_installed = True
        except NoSolverAvailableError:
            is_installed = False
        print("  %s%s" % (solver.ljust(10), is_installed))

        if solver in required_solvers and not is_installed:
            raise Exception("Was expecting to find %s installed" % solver)


def parse_options():
    parser = argparse.ArgumentParser(description='Install SMT Solvers.\n\n'
                                     'This script installs the solvers specified'
                                     ' on the command line or in the environment'
                                     ' variable PYSMT_SOLVER if not already '
                                     'instaled on the system.')

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

    parser.add_argument('--bindings-path', dest='bindings_path',
                        type=str, default="~/.smt_solvers/python_bindings",
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

    # Env variable controlling the solvers to be installed or checked
    requested_solvers = get_requested_solvers()


    solvers_to_install = []
    all_solvers = options.all_solvers
    for i in INSTALLERS:
        name = i.InstallerClass.SOLVER
        if all_solvers or getattr(options, name) or name in requested_solvers:
            solvers_to_install.append(i)

    if options.check:
        check_installed([x.InstallerClass.SOLVER for x in solvers_to_install])
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

        # This should work on any platform
        install_dir= os.path.expanduser(options.install_path)
        if not os.path.exists(install_dir):
            os.mkdir(install_dir)

        # This should work on any platform
        bindings_dir= os.path.expanduser(options.bindings_path)
        if not os.path.exists(bindings_dir):
            os.mkdir(bindings_dir)

        for i in solvers_to_install:
            installer = i.InstallerClass(install_dir=install_dir,
                                         bindings_dir=bindings_dir,
                                         solver_version=i.version,
                                         mirror_link=mirror_url,
                                         **i.extra_params)
            installer.install(force_redo=options.force_redo)


if __name__ == "__main__":
    main()
