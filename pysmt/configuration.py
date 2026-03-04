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
"""Utils to configure pySMT.

The following is an example of configuration file.

[global]
use_infix_notation: true
solver_preference_list: msat z3 cvc4 z3-smt mathsat-smt

[smtlibsolver z3-smt]
command: z3 -smt2 -in
logics: QF_UFLIRA UFLIRA


[smtlibsolver mathsat-smt]
command: mathsat
logics: QF_UFLIRA



Wrapper solvers are defined using the smtlibsolver section + the name
of the solver.
"""

import os.path
import configparser as cp
from warnings import warn

from pysmt.logics import get_logic_by_name
from pysmt.exceptions import PysmtIOError

def configure_environment(config_filename, environment):
    """
    Reads a configuration file from the given path and configures the
    given environment accordingly.
    """
    factory = environment.factory

    if not os.path.exists(config_filename):
        raise PysmtIOError("File '%s' does not exists." % config_filename)

    # We do not use variable inside the config file
    config = cp.RawConfigParser()
    config.read(config_filename)

    new_solvers_sections = [s for s in config.sections()
                            if s.lower().startswith("smtlibsolver ")]

    for s in new_solvers_sections:
        name = s[len("smtlibsolver "):]

        cmd = config.get(s, "command")
        assert cmd is not None, ("Missing 'command' value in definition"
                                 "of '%s' solver" % name)

        logics_string = config.get(s, "logics")
        if logics_string is None:
            warn("Missing 'logics' value in definition of '%s' solver" % name,
                 stacklevel=2)
            continue

        logics = [get_logic_by_name(l) for l in logics_string.split()]

        factory.add_generic_solver(name, cmd.split(), logics)


    if "global" in config.sections():
        infix = config.get("global", "use_infix_notation")
        pref_list = config.get("global", "solver_preference_list")
        if infix is not None:
            if infix.lower() == "true":
                environment.enable_infix_notation = True
            elif infix.lower() == "false":
                environment.enable_infix_notation = True
            else:
                warn("Unknown value for 'use_infix_notation': %s" % infix,
                     stacklevel=2)

        if pref_list is not None:
            prefs = pref_list.split()
            for s in prefs:
                if s not in factory.all_solvers():
                    warn("Unknown solver '%s' in solver_preference_list" % s,
                         stacklevel=2)

            for s in factory.all_solvers():
                if s not in prefs:
                    warn("Solver '%s' is not in the preference list, "\
                         "and will be disabled." % s,
                         stacklevel=2)

            factory.set_solver_preference_list(prefs)



def write_environment_configuration(config_filename, environment):
    """
    Dumps the configuration of the given environment to the specified
    file. The file can then be re-read with the :py:func:`configure_environment`
    function.

    """
    factory = environment.factory

    config = cp.RawConfigParser()

    config.add_section("global")
    inf = "true" if environment.enable_infix_notation else "false"
    pl = " ".join(factory.solver_preference_list)
    config.set("global", "use_infix_notation", inf)
    config.set("global", "solver_preference_list", pl)

    for s in factory.all_solvers():
        if factory.is_generic_solver(s):
            args,logics = factory.get_generic_solver_info(s)

            sec_name = 'smtlibsolver %s' % s
            config.add_section(sec_name)

            config.set(sec_name, "command", " ".join(args))
            config.set(sec_name, "logics", " ".join(str(l) for l in logics))


    # Writing the configuration to file
    with open(config_filename, 'wt') as configfile:
        config.write(configfile)
