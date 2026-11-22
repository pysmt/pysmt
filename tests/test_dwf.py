#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
from pysmt.test import TestCase
from pysmt.operators import CUSTOM_NODE_TYPES, new_node_type, all_types
from pysmt.type_checker import SimpleTypeChecker
from pysmt.printers import HRPrinter
from pysmt.shortcuts import get_env, Symbol
from pysmt.exceptions import UnsupportedOperatorError


class TestDwf(TestCase):
    # NOTE: We enforce order of execution of the tests, since in the
    # other test we define a custom type.
    def test_00_new_node_type(self):
        self.assertNotIn(199, CUSTOM_NODE_TYPES,
                        "Initially there should be no custom node with id 199")
        idx = new_node_type(node_id=199)
        self.assertIsNotNone(idx)
        with self.assertRaises(AssertionError):
            new_node_type(idx)

        n = new_node_type(idx+100)
        self.assertEqual(n, idx+100)

    def test_01_dwf(self):
        # Ad-hoc method to handle printing of the new node
        def hrprinter_walk_XOR(self, formula):
            self.stream.write("(")
            yield formula.arg(0)
            self.stream.write(" *+* ")
            yield formula.arg(1)
            self.stream.write(")")

        # Shortcuts for function in env
        add_dwf = get_env().add_dynamic_walker_function
        create_node = get_env().formula_manager.create_node

        # Define the new node type and register the walkers in the env
        XOR = new_node_type()
        add_dwf(XOR, SimpleTypeChecker, SimpleTypeChecker.walk_bool_to_bool)
        add_dwf(XOR, HRPrinter, hrprinter_walk_XOR)

        # Create a test node (This implicitely calls the Type-checker)
        x = Symbol("x")
        f1 = create_node(node_type=XOR, args=(x,x))
        self.assertIsNotNone(f1)

        # String conversion should use the function defined above.
        s_f1 = str(f1)
        self.assertEqual(s_f1, "(x *+* x)")

        # We did not define an implementation for the Simplifier
        with self.assertRaises(UnsupportedOperatorError):
            f1.simplify()

    def test_02_all_types(self):
        old_types_set = set(all_types())
        new_t = new_node_type()
        new_types_set = set(all_types())
        self.assertEqual(new_types_set - old_types_set, set([new_t]))

    def test_03_dwf_is_environment_local(self):
        # A DWF registered in one environment must not leak into another.
        # Handlers are dispatched via Walker.super through the walker's
        # own env, not by mutating the (process-global) walker class.
        from pysmt.environment import Environment
        from pysmt.printers import HRPrinter

        def make_printer(sep):
            def hrprinter_walk_XOR(self, formula):
                self.stream.write("(")
                yield formula.arg(0)
                self.stream.write(sep)
                yield formula.arg(1)
                self.stream.write(")")
            return hrprinter_walk_XOR

        XOR = new_node_type()
        env1 = Environment()
        env2 = Environment()

        # Both envs must be able to build the node, so both get a
        # type-checker handler. Only env1 gets a printer handler.
        for env in (env1, env2):
            env.add_dynamic_walker_function(
                XOR, SimpleTypeChecker, SimpleTypeChecker.walk_bool_to_bool)
        env1.add_dynamic_walker_function(XOR, HRPrinter, make_printer(" *+* "))

        x1 = env1.formula_manager.Symbol("x")
        f1 = env1.formula_manager.create_node(node_type=XOR, args=(x1, x1))
        self.assertEqual(env1.serializer.serialize(f1), "(x *+* x)")

        # The handler registered on env1 must NOT leak into env2.
        x2 = env2.formula_manager.Symbol("x")
        f2 = env2.formula_manager.create_node(node_type=XOR, args=(x2, x2))
        with self.assertRaises(UnsupportedOperatorError):
            env2.serializer.serialize(f2)

        # env2 can register its own, independent handler for the same
        # (nodetype, walker) pair, and env1 stays unaffected.
        env2.add_dynamic_walker_function(XOR, HRPrinter, make_printer(" XOR "))
        self.assertEqual(env2.serializer.serialize(f2), "(x XOR x)")
        self.assertEqual(env1.serializer.serialize(f1), "(x *+* x)")

        # Redefining the same (nodetype, walker) within one env is caught.
        with self.assertRaises(AssertionError):
            env1.add_dynamic_walker_function(XOR, HRPrinter, make_printer("!"))
