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
from tempfile import mkstemp

from six.moves import cStringIO

import pysmt.logics as logics
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.test.examples import get_example_formulae
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.shortcuts import Iff
from pysmt.shortcuts import read_smtlib, write_smtlib
from pysmt.exceptions import PysmtSyntaxError

class TestSMTParseExamples(TestCase):

    def test_parse_examples(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic == logics.QF_BV:
                # See test_parse_examples_bv
                continue
            buf = cStringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf)
            #print(buf)

            buf.seek(0)
            parser = SmtLibParser()
            script_in = parser.get_script(buf)
            f_in = script_in.get_last_formula()
            self.assertEqual(f_in.simplify(), f_out.simplify())


    @skipIfNoSolverForLogic(logics.QF_BV)
    def test_parse_examples_bv(self):
        """For BV we represent a superset of the operators defined in SMT-LIB.

        We verify the correctness of the serialization process by
        checking the equivalence of the original and serialized
        expression.
        """
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic != logics.QF_BV:
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
            if logic == logics.QF_BV:
                # See test_parse_examples_daggified_bv
                continue
            buf_out = cStringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out, daggify=True)
            buf_in = cStringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()
            self.assertEqual(f_in.simplify(), f_out.simplify())

    @skipIfNoSolverForLogic(logics.QF_BV)
    def test_parse_examples_daggified_bv(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic != logics.QF_BV:
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

    def test_dumped_logic(self):
        # Dumped logic matches the logic in the example
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            buf_out = cStringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out)
            buf_in = cStringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            for cmd in script_in:
                if cmd.name == "set-logic":
                    logic_in = cmd.args[0]
                    if logic == logics.QF_BOOL:
                        self.assertEqual(logic_in, logics.QF_UF)
                    elif logic == logics.BOOL:
                        self.assertEqual(logic_in, logics.LRA)
                    else:
                        self.assertEqual(logic_in, logic, script_in)
                    break
            else: # Loops exited normally
                print("-"*40)
                print(script_in)

    def test_read_and_write_shortcuts(self):
        fs = get_example_formulae()

        fdi, tmp_fname = mkstemp()
        os.close(fdi) # Close initial file descriptor
        for (f_out, _, _, _) in fs:
            write_smtlib(f_out, tmp_fname)
            # with open(tmp_fname) as fin:
            #     print(fin.read())

            f_in = read_smtlib(tmp_fname)
            self.assertEqual(f_out.simplify(), f_in.simplify())
        # Clean-up
        os.remove(tmp_fname)

    def test_incomplete_stream(self):
        txt = """
        (declare-fun A () Bool)
        (declare-fun B () Bool)
        (assert (and A
        """
        parser = SmtLibParser()
        with self.assertRaises(PysmtSyntaxError):
            parser.get_script(cStringIO(txt))

if __name__ == "__main__":
    main()
