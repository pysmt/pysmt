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
