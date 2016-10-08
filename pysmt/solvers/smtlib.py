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
class SmtLibSolver(object):
    #
    # SMT-LIB 2 Interface
    #
    def set_logic(self, logic):
        """ Defines the logic in use.

        E.g., set_logic("QF_LIA")

        Restrictions: Can be executed only once.

        :param logic: The logic in use
        :type logic:  String
        :returns: True on success,
                  False if the logic is not supported
        """
        raise NotImplementedError

    def declare_fun(self, symbol):
        """ Declare a function symbol.

        Restrictions: Only after set-logic.

        :param symbol: Symbol to be declared
        :type name:  Pysmt symbol
        :returns: None - might raise exceptions
        """
        raise NotImplementedError

    def declare_const(self, symbol):
        """ Declares a constant symbol.

        Restrictions: Only after set-logic.

        :param symbol: Symbol to be declared
        :type name:  Pysmt symbol
        :returns: None
        """
        raise NotImplementedError

    def define_fun(self, name, args, rtype, expr):
        """ Declare an interpreted function. Can be used to build abbreviations.

        Restrictions: Only after set-logic.

        :param name: Name of the function
        :type name:  String
        :param args: Name and Type of the arguments of the function
        :type args: List of tuples (name, type)
        :param rtype: Return type
        :type rtype: Sort
        :param expr: Expression to associate with the functino
        :type expr: FNode
        :returns: None - might raise exceptions
        """
        raise NotImplementedError

    def declare_sort(self, name, cardinality):
        """ Declares a new sort with the given name and cardinality.

        Restrictions: Only after set-logic.

        :returns: None - might raise exception
        """
        raise NotImplementedError

    def define_sort(self, name, args, sort_expr):
        """ Declares a symbol as an abreviation for a sort-expression.

        Restrictions: Only after set-logic.
        :returns: None - might raise exception
        """
        raise NotImplementedError

    def assert_(self, expr, named=None):
        """ Assert the given expression.

        Optionally provides a name to the terms.

        Restrictions: Only after set-logic.
        :returns: None - might raise exception
        """
        raise NotImplementedError

    def get_assertions(self):
        """ Returns a list of asserted expressions.

        Restrictions: Only after set-logic.
        """
        raise NotImplementedError

    def check_sat(self):
        """ Checks the satisfiability of the formula.

        Restrictions: Only after set-logic.

        :returns: SAT, UNSAT, Unknown
        """
        raise NotImplementedError

    def get_proof(self):
        """ Returns a proof of unsatisfiability.

        Restrictions: Requires option :produce-proofs to be set and can be
                      called only after check-sat returned unsat, if no
                      change to the assertion set occurred.

        Note: The structure of the returned proof is Solver dependent.

        """
        raise NotImplementedError

    def get_unsat_core(self):
        """ Returns the unsat cores.

        Restrictions: Requires option :produce-unsat-cores to be set true and can
                      be called only after check-sat returned unsat, if no
                      change to the assertion set occurred.

        Note: Requires elements to be named.
        """
        raise NotImplementedError

    def get_values(self, exprs):
        """ Returns the value of the expressions if a model was found.

        Restrictions: Requires option :produce-models to be set to true and can
                      be called only after check-sat returned sat or unknown,
                      if no change to the assertion set occurred.

        :type exprs: List of FNodes
        :returns: A dictionary associating to each expr a value
        :rtype: dict
        """
        raise NotImplementedError

    def get_assignment(self):
        """ Returns an assignment for the named terms.

        Restrictions: Requires option :produce-assignments to be set to true and
                      can be called only after check-sat returned sat or unknown
                      if no change to the assertion set occurred.

        Note: Requires elements to be named
        """
        raise NotImplementedError

    def push(self, levels=1):
        """ Push the current context of the given number of levels.

        Restrictions: after set-logic
        """
        raise NotImplementedError

    def pop(self, levels=1):
        """ Pop the context of the given number of levels.

        Restrictions: after set-logic
        """
        raise NotImplementedError

    def get_option(self, name):
        """ Gets the value of the given option from the solver."""
        raise NotImplementedError

    def set_option(self, name, value):
        """ Sets the given value for the option in the solver.

        SMTLIB-defined Options:

        +---------------------------+----------+---------+----------+
        | Name                      | Required | Type    | Default  |
        +===========================+==========+=========+==========+
        | print-success             | required | boolean | true     |
        | regular-output-channel    | required | string  | "stdout" |
        | diagnostic-output-channel | required | string  | "stderr" |
        | expand-definitions        | optional | boolean | false    |
        | interactive-mode          | optional | boolean | false    |
        | produce-proofs            | optional | boolean | false    |
        | produce-unsat-cores       | optional | boolean | false    |
        | produce-models            | optional | boolean | false    |
        | produce-assignments       | optional | boolean | false    |
        | random-seed               | optional | numeral | 0        |
        | verbosity                 | optional | numeral | 0        |
        +---------------------------+----------+---------+----------+
        """
        raise NotImplementedError

    def get_info(self, name):
        """ Gets the value of a given information. """
        raise NotImplementedError

    def set_info(self, name, value):
        """ Sets the value for a given information.

        Required (by SMT):
        * :name <string>
        * :authors <string>
        * :version <string>
        Optional
        * :error-behavior
        * :reason-unknown
        * :all-statistics
        """
        raise NotImplementedError

    def exit(self):
        """Destroys the solver."""
        raise NotImplementedError

    #
    # End of SMT-LIB 2 interface
    #


class SmtLibIgnoreMixin(SmtLibSolver):
    def set_logic(self, logic):
        return None

    def declare_fun(self, symbol):
        return None

    def declare_const(self, symbol):
        return None

    def define_fun(self, name, args, rtype, expr):
        return None

    def declare_sort(self, name, cardinality):
        return None

    def define_sort(self, name, args, sort_expr):
        return None

    def assert_(self, expr, named=None):
        return None

    def get_assertions(self):
        return None

    def check_sat(self):
        return None

    def get_proof(self):
        return None

    def get_unsat_core(self):
        return None

    def get_values(self, exprs):
        return None

    def get_assignment(self):
        return None

    def push(self, levels=1):
        return None

    def pop(self, levels=1):
        return None

    def get_option(self, name):
        return None

    def set_option(self, name, value):
        return None

    def get_info(self, name):
        return None

    def set_info(self, name, value):
        return None

    def exit(self):
        return None


class SmtLibBasicSolver(SmtLibSolver):
    def assert_(self, expr, named=None):
        return self.add_assertion(expr, named)

    def check_sat(self):
        return self.solve()

    def get_values(self, exprs):
        return self.get_values(exprs)

    def push(self, levels=1):
        return self.push(levels)

    def pop(self, levels=1):
        return self.pop(levels)

    def exit(self):
        return self.exit()
