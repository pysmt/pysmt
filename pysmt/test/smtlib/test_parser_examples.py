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
from six.moves import cStringIO

from pysmt.test import TestCase, skipIfNoSolverForLogic
from pysmt.test.examples import get_example_formulae
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.shortcuts import Iff
from pysmt.logics import QF_BV


class TestSMTParseExamples(TestCase):

    def test_parse_examples(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic == QF_BV:
                # See test_parse_examples_bv
                continue
            buf_out = cStringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out)

            buf_in = cStringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()

            self.assertEqual(f_in, f_out)


    @skipIfNoSolverForLogic(QF_BV)
    def test_parse_examples_bv(self):
        """For BV we represent a superset of the operators defined in SMT-LIB.

        We verify the correctness of the serialization process by
        checking the equivalence of the original and serialized
        expression.
        """
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic != QF_BV:
                continue
            buf_out = cStringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out)

            buf_in = cStringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()

            self.assertValid(Iff(f_in, f_out))


    def test_parse_examples_daggified(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic == QF_BV:
                # See test_parse_examples_daggified_bv
                continue
            buf_out = cStringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out, daggify=True)
            buf_in = cStringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()
            self.assertEqual(f_in, f_out)

    @skipIfNoSolverForLogic(QF_BV)
    def test_parse_examples_daggified_bv(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic != QF_BV:
                # See test_parse_examples_daggified
                continue
            buf_out = cStringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out, daggify=True)
            buf_in = cStringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()
            self.assertValid(Iff(f_in, f_out), f_in.serialize())
