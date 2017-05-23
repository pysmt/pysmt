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
from pysmt.type_checker import SimpleTypeChecker
from pysmt.printers import HRPrinter, HRSerializer
from pysmt.shortcuts import get_env, Symbol, reset_env
from pysmt.exceptions import UnsupportedOperatorError
from pysmt.environment import Environment
from pysmt.operators import new_node_type, all_types


class TestExtendSuper(TestCase):
    def test_new_node_type(self):
        old = list(all_types())
        idx = new_node_type(node_str="xor")
        self.assertIsNotNone(idx)
        self.assertNotIn(idx, old)
        with self.assertRaises(AssertionError):
            new_node_type(idx)
        XOR = idx

        # Ad-hoc method to handle printing of the new node
        def hrprinter_walk_xor(self, formula):
            self.stream.write("(")
            yield formula.arg(0)
            self.stream.write(" *+* ")
            yield formula.arg(1)
            self.stream.write(")")

        SimpleTypeChecker.walk_xor = SimpleTypeChecker.walk_bool_to_bool
        HRPrinter.walk_xor = hrprinter_walk_xor

        # Reset the env to recreate the TypeChecker and HRPrinter
        reset_env()

        # Shortcuts for function in env
        create_node = get_env().formula_manager.create_node
        # Create a test node (This implicitly calls the Type-checker)
        x = Symbol("x")
        f1 = create_node(node_type=XOR, args=(x,x))
        self.assertIsNotNone(f1)

        # String conversion should use the function defined above.
        s_f1 = str(f1)
        self.assertEqual(s_f1, "(x *+* x)")

        # We did not define an implementation for the Simplifier
        with self.assertRaises(UnsupportedOperatorError):
            f1.simplify()

        # Clean-up
        del SimpleTypeChecker.walk_xor
        del HRPrinter.walk_xor

        class MySimpleTypeChecker(SimpleTypeChecker):
            walk_xor = SimpleTypeChecker.walk_bool_to_bool

        class MyHRPrinter(HRPrinter):
            def walk_xor(self, formula):
                return self.walk_nary(formula, " *+* ")

        class MyHRSerializer(HRSerializer):
            PrinterClass = MyHRPrinter

        class MyEnv(Environment):
            TypeCheckerClass = MySimpleTypeChecker
            HRSerializerClass = MyHRSerializer

        with MyEnv() as myenv:
            create_node = myenv.formula_manager.create_node
            # Create a test node (This implicitly calls the Type-checker)
            x = Symbol("x")
            f1 = create_node(node_type=XOR, args=(x,x))
            self.assertIsNotNone(f1)

            # String conversion should use the function defined above.
            s_f1 = str(f1)
            self.assertEqual(s_f1, "(x *+* x)")

            # We did not define an implementation for the Simplifier
            with self.assertRaises(UnsupportedOperatorError):
                f1.simplify()

        return
