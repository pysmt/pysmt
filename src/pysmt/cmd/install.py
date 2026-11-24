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

import argparse
import os
import subprocess
import sys
from collections import namedtuple

from pysmt import __version__ as pysmt_version
from pysmt.cmd.installers import (
    MSatInstaller,
    OptiMSatInstaller,
    PicoSATInstaller,
    YicesInstaller,
)
from pysmt.cmd.installers.base import installed_version, pip_install
from pysmt.environment import get_env
from pysmt.exceptions import PysmtException

# Solvers installed by pip from exact-pinned requirements. The version shown by
# --check is the installed version of `distribution`.
PipSolver = namedtuple("PipSolver", ["name", "distribution", "requirements"])
# Solvers downloaded and built by an installer class (see pysmt.cmd.installers)
BuildSolver = namedtuple(
    "BuildSolver", ["name", "InstallerClass", "version", "extra_params"]
)

SOLVERS = [
    BuildSolver("msat", MSatInstaller, "5.6.20", {}),
    PipSolver("cvc5", "cvc5", ["cvc5==1.4.2"]),
    PipSolver("z3", "z3-solver", ["z3-solver==5.4.1.0"]),
    BuildSolver(
        "yices",
        YicesInstaller,
        "2.8.0",
        {
            "yices_api_version": "1.1.6",
            # (system, machine) -> platform of SRI's prebuilt archive for this version
            "binaries": {
                ("linux", "x86_64"): "x86_64-pc-linux-gnu",
                ("darwin", "arm64"): "aarch64-apple-darwin25.6.0",
                ("darwin", "x86_64"): "x86_64-apple-darwin25.6.0",
            },
        },
    ),
    PipSolver("btor", "pyboolector", ["pyboolector==3.2.4.38488416565"]),
    BuildSolver(
        "picosat", PicoSATInstaller, "965", {"pypicosat_minor_version": "1708010052"}
    ),
    PipSolver("bdd", "repycudd", ["repycudd==3.1.0"]),
    BuildSolver("optimsat", OptiMSatInstaller, "1.7.5", {}),
]


def get_requested_solvers():
    """Parses the PYSMT_SOLVER env variable to extract requirements to fulfill"""

    requested_solvers_str = os.environ.get("PYSMT_SOLVER")
    requested_solvers = []
    if requested_solvers_str is not None:
        keys = requested_solvers_str.split(",")
        requested_solvers = [x.lower().strip() for x in keys]
        if "all" in requested_solvers:
            requested_solvers = [x.name for x in SOLVERS]
    return requested_solvers


def make_installer(solver, install_dir, target):
    return solver.InstallerClass(
        install_dir=install_dir,
        target=target,
        solver_version=solver.version,
        **solver.extra_params,
    )


def check_installed(required_solvers, install_dir, target):
    """Checks which solvers are visible to pySMT."""

    if target is not None:
        sys.path.insert(0, target)

    # Check which solvers are accessible from the Factory
    pypath_solvers = get_env().factory.all_solvers()

    global_solvers_status = []
    print("Installed Solvers:")
    for s in SOLVERS:
        if isinstance(s, PipSolver):
            version = installed_version(s.distribution)
        else:
            installer = make_installer(s, install_dir, target)
            version = installer.get_installed_version()
        global_solvers_status.append((s.name, version is not None, version))

    for solver in required_solvers:
        if solver not in pypath_solvers:
            raise PysmtException(f"Was expecting to find {solver} installed")

    #
    # Output information
    #
    for solver, is_installed, version in global_solvers_status:
        msg = f"  {solver.ljust(10)}{is_installed} "
        msg += (f"({version})").ljust(20)
        if solver not in pypath_solvers:
            msg += "Not in Python's path!"
        print(msg)
    print("")

    print("Solvers: {}".format(", ".join(name for name in pypath_solvers)))
    qes = get_env().factory.all_quantifier_eliminators()
    print("Quantifier Eliminators: {}".format(", ".join(name for name in qes)))

    ucs = get_env().factory.all_unsat_core_solvers()
    print("UNSAT-Cores: {}".format(", ".join(name for name in ucs)))

    interps = get_env().factory.all_interpolators()
    print("Interpolators: {}".format(", ".join(name for name in interps)))

    opts = get_env().factory.all_optimizers()
    print("Optimizers: {}".format(", ".join(name for name in opts)))


def parse_options():
    parser = argparse.ArgumentParser(
        description="Install SMT Solvers.\n\n"
        "This script installs the solvers specified"
        " on the command line or in the environment"
        " variable PYSMT_SOLVER into the Python"
        " interpreter running it."
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"%(prog)s {pysmt_version}",
    )

    for s in SOLVERS:
        parser.add_argument(
            f"--{s.name}",
            dest=s.name,
            action="store_true",
            default=False,
            help=f"Install {s.name}",
        )

    parser.add_argument(
        "--all",
        dest="all_solvers",
        action="store_true",
        default=False,
        help="Install all the solvers",
    )

    parser.add_argument(
        "--force",
        dest="force_redo",
        action="store_true",
        default=False,
        help="Reinstall the solvers even if already installed",
    )

    parser.add_argument(
        "--check",
        dest="check",
        action="store_true",
        default=False,
        help="Checks the installation of the solvers",
    )

    parser.add_argument(
        "--confirm-agreement",
        dest="skip_intro",
        action="store_true",
        default=False,
        help="Confirm that you agree with the licenses of the"
        " solvers and skip the interactive question",
    )

    install_path_default = os.path.join("~", ".smt_solvers")
    parser.add_argument(
        "--install-path",
        dest="install_path",
        type=str,
        default=install_path_default,
        help="The folder used to download and build the solvers that are not"
        f" installed from PyPI (defaults to: {install_path_default!r})",
    )

    parser.add_argument(
        "--target",
        dest="target",
        metavar="DIR",
        type=str,
        default=None,
        help="Install the solvers into DIR instead of the current environment."
        " DIR must then be added to PYTHONPATH.",
    )

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
    res = input("Continue? [Y]es/[N]o: ").strip().lower()

    if res not in ("y", "yes"):
        exit(-1)


def main():
    options = parse_options()

    # This should work on any platform
    install_dir = os.path.expanduser(options.install_path)
    if not os.path.exists(install_dir):
        os.makedirs(install_dir)

    target = options.target
    if target is not None:
        target = os.path.abspath(os.path.expanduser(target))
        os.makedirs(target, exist_ok=True)

    solvers_to_install = []
    all_solvers = options.all_solvers
    for s in SOLVERS:
        if all_solvers or getattr(options, s.name):
            solvers_to_install.append(s)

    # Env variable controlling the solvers to be installed or checked
    requested_solvers = get_requested_solvers()
    if len(solvers_to_install) != 0 and len(requested_solvers) != 0:
        print(
            "Warning: Solvers specified on the command line, "
            "ignoring env variable 'PYSMT_SOLVER'"
        )
    if len(solvers_to_install) == 0:
        # No solver requested from cmd-line, checking ENV
        for s in SOLVERS:
            if s.name in requested_solvers:
                solvers_to_install.append(s)

    if options.check:
        check_installed(
            [x.name for x in solvers_to_install],
            install_dir=install_dir,
            target=target,
        )
        exit(0)

    if len(solvers_to_install) == 0:
        print(f"Nothing to do.\nTry with '{sys.argv[0]} --help'")
        exit(0)

    # Do the actual install
    if not options.skip_intro:
        print_welcome()

    try:
        for s in solvers_to_install:
            if isinstance(s, PipSolver):
                pip_install(s.requirements, target=target, force=options.force_redo)
            else:
                installer = make_installer(s, install_dir, target)
                installer.install(force_redo=options.force_redo)
    except (PysmtException, subprocess.CalledProcessError) as e:
        sys.exit(f"Error: {e}")
