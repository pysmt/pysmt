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
"""A SolverOptions class is associated to each Solver to handle its
configuration. We consider two types of options. The first type is
available in most solvers, while the second type is solver-specific.

The first type is handled and documented in the base class
SolverOptions: generate_models, incremental etc.
The second type is handled within the dictionary "solver_options".

To use the Options it is necessary to:

* Define the class attribute OptionsClass within the Solver Class
* Validate the options during in SolverOptions.__init__
* Implement the method SolverOptions.__call__
* During Solver.__init__ the solver must call the option class::

    self.options(self)

"""

import abc

class SolverOptions(object):
    """Solver Options shared by most solvers.

    * generate_models : True, False
      Enable model generation. Needed for get_value, get_model etc.

    * incremental: True, False
      Enable incremental interface (push, pop)

    * unsat_cores_mode: None, "named", "all"
      Enable UNSAT core extraction using "named" or "all" strategy.

    * random_seed: None, integer
      Sets the random seed for the solver

    * solver_options: dictionary
      Provides solver specific options

    """
    __metaclass__ = abc.ABCMeta

    def __init__(self, generate_models=True, incremental=True,
                 unsat_cores_mode=None, random_seed=None,
                 solver_options=None):

        if generate_models not in (True, False):
            raise ValueError("Invalid value %s for 'generate_models'" \
                             % generate_models)
        self.generate_models = generate_models

        if incremental not in (True, False):
            raise ValueError("Invalid value %s for 'incremental'" \
                             % incremental)
        self.incremental = incremental

        if unsat_cores_mode not in (None, "named", "all"):
            raise ValueError("Invalid value %s for 'unsat_cores_mode'" \
                             % unsat_cores_mode)
        self.unsat_cores_mode = unsat_cores_mode

        if random_seed is not None and type(random_seed) != int:
            raise ValueError("Invalid value %s for 'random_seed'" \
                             % random_seed)
        self.random_seed = random_seed

        if solver_options is not None:
            try:
                solver_options = dict(solver_options)
            except:
                raise ValueError("Invalid value %s for 'solver_options'" \
                                 % solver_options)
        else:
            solver_options = dict()
        self.solver_options = solver_options

    @abc.abstractmethod
    def __call__(self, solver):
        """Handle the setting options within solver"""
        raise NotImplementedError

    def as_kwargs(self):
        """Construct a dictionary object that can be used as **kwargs.

        This can be used to duplicate the options.
        """
        kwargs = {}
        for k in ("generate_models", "incremental", "unsat_cores_mode",
                  "random_seed", "solver_options"):
            v = getattr(self, k)
            kwargs[k] = v
        return kwargs

# EOC SolverOptions
