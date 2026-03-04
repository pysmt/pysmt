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
import os

from io import StringIO

from pysmt.test.smtlib.parser_utils import SMTLIB_DIR
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.annotations import Annotations
from pysmt.shortcuts import Symbol
from pysmt.test import TestCase, main

class TestBasic(TestCase):

    def test_basic(self):
        ann = Annotations()
        a = Symbol("a")
        next_a = Symbol("next(a)")
        init_a = Symbol("init(a)")

        ann.add(a, "next", next_a)
        ann.add(a, "init", init_a)
        ann.add(a, "related", next_a)
        ann.add(a, "related", init_a)

        self.assertIn(a, ann)
        self.assertEqual(set([next_a]), ann.annotations(a)["next"])
        self.assertEqual(set([init_a]), ann.annotations(a)["init"])
        self.assertEqual(set([init_a, next_a]), ann.annotations(a)["related"])
        self.assertEqual(set([a]), ann.all_annotated_formulae("next"))
        self.assertEqual(set([a]), ann.all_annotated_formulae("init"))
        self.assertEqual(set([a]), ann.all_annotated_formulae("related"))
        self.assertEqual(set(), ann.all_annotated_formulae("non-existent"))

    def test_remove(self):
        ann = Annotations()
        a = Symbol("a")
        next_a = Symbol("next(a)")
        init_a = Symbol("init(a)")

        ann.add(a, "next", next_a)
        ann.add(a, "init", init_a)
        ann.add(a, "related", next_a)
        ann.add(a, "related", init_a)

        self.assertIn(a, ann)
        ann.remove(a)
        self.assertNotIn(a, ann)

        self.assertEqual(None, ann.annotations(a))
        self.assertEqual(set([]), ann.all_annotated_formulae("next"))
        self.assertEqual(set([]), ann.all_annotated_formulae("init"))
        self.assertEqual(set([]), ann.all_annotated_formulae("related"))
        self.assertEqual(set(), ann.all_annotated_formulae("non-existent"))

    def test_remove_annotation(self):
        ann = Annotations()
        a = Symbol("a")
        next_a = Symbol("next(a)")
        init_a = Symbol("init(a)")

        ann.add(a, "next", next_a)
        ann.add(a, "init", init_a)
        ann.add(a, "related", next_a)
        ann.add(a, "related", init_a)

        ann.remove_annotation(a, "next")

        self.assertNotIn("next", ann.annotations(a))
        self.assertEqual(set([init_a]), ann.annotations(a)["init"])
        self.assertEqual(set([init_a, next_a]), ann.annotations(a)["related"])
        self.assertEqual(set([]), ann.all_annotated_formulae("next"))
        self.assertEqual(set([a]), ann.all_annotated_formulae("init"))
        self.assertEqual(set([a]), ann.all_annotated_formulae("related"))
        self.assertEqual(set(), ann.all_annotated_formulae("non-existent"))

    def test_remove_value(self):
        ann = Annotations()
        a = Symbol("a")
        next_a = Symbol("next(a)")
        init_a = Symbol("init(a)")

        ann.add(a, "next", next_a)
        ann.add(a, "init", init_a)
        ann.add(a, "related", next_a)
        ann.add(a, "related", init_a)

        self.assertNotEqual(ann.annotations(a)["init"], ann.annotations(a)["related"])
        ann.remove_value(a, "related", next_a)
        self.assertEqual(ann.annotations(a)["related"], ann.annotations(a)["init"])

    def test_vmt(self):
        parser = SmtLibParser()
        fname = os.path.join(SMTLIB_DIR, "small_set/vmt/c432_0f.vmt")
        script = parser.get_script_fname(fname)

        ann = script.annotations

        self.assertIn("A_1__AT0 ->", str(ann))

        a1 = Symbol("A_1__AT0")

        self.assertIn(a1, ann)
        self.assertTrue(ann.has_annotation(a1, "next"))
        self.assertFalse(ann.has_annotation(a1, "non-existent"))
        self.assertTrue(ann.has_annotation(a1, "next", "A_1__AT1"))
        self.assertFalse(ann.has_annotation(a1, "next", "non-existent"))

        self.assertIn("A_1__AT1", ann.annotations(a1)["next"])
        self.assertIn("A_1__AT1", ann[a1]["next"])

        curr_a1 = ann.all_annotated_formulae("next", "A_1__AT1")
        self.assertEqual(curr_a1, set([a1]))

    def test_interpreting_annotations(self):
        source ="""\
(declare-fun |"v__AT0"| () Bool)
(declare-fun |"v__AT1"| () Bool)
(define-fun .def_1 () Bool (! |"v__AT0"| :next |"v__AT1"|))
"""
        buf = StringIO(source)
        parser = SmtLibParser()
        script = parser.get_script(buf)
        ann = script.annotations
        v0 = self.env.formula_manager.get_symbol('"v__AT0"')
        v1_str = next(iter(ann[v0]["next"]))
        self.env.formula_manager.get_symbol(v1_str)
        self.assertEqual(v1_str, '"v__AT1"')


    def test_complex_annotations_values(self):
        source ="""\
(declare-fun |"v__AT0"| () Bool)
(define-fun .def_1 () Bool (! |"v__AT0"| :next (+ 1     meaningless)))
"""
        buf = StringIO(source)
        parser = SmtLibParser()
        script = parser.get_script(buf)
        ann = script.annotations
        v0 = self.env.formula_manager.get_symbol('"v__AT0"')
        v1_str = next(iter(ann[v0]["next"]))
        self.assertEqual(v1_str, "(+ 1     meaningless)")


    def test_annotations_colon_values(self):
        source ="""\
(declare-fun |"v__AT0"| () Bool)
(define-fun .def_1 () Bool (! |"v__AT0"| :next :this_is_considered_a_value))
"""
        buf = StringIO(source)
        parser = SmtLibParser()
        script = parser.get_script(buf)
        ann = script.annotations
        v0 = self.env.formula_manager.get_symbol('"v__AT0"')
        v1_str = next(iter(ann[v0]["next"]))
        self.assertEqual(v1_str, ":this_is_considered_a_value")


if __name__ == '__main__':
    main()
