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
from pysmt.shortcuts import Symbol, Int, And, Or, Not, GT
from pysmt.typing import INT
from pysmt.oracles import SizeOracle
from pysmt.test import TestCase, main
from pysmt.test.examples import get_example_formulae

class TestSize(TestCase):

    def test_leaf(self):
        varA = Symbol("A")
        self.assertEqual(varA.size(), 1)
        self.assertEqual(varA.size(SizeOracle.MEASURE_TREE_NODES), 1)
        self.assertEqual(varA.size(SizeOracle.MEASURE_DAG_NODES), 1)
        self.assertEqual(varA.size(SizeOracle.MEASURE_LEAVES), 1)
        self.assertEqual(varA.size(SizeOracle.MEASURE_DEPTH), 1)
        self.assertEqual(varA.size(SizeOracle.MEASURE_SYMBOLS), 1)

    def test_const_leaf(self):
        f = Int(0)
        self.assertEqual(f.size(), 1)
        self.assertEqual(f.size(SizeOracle.MEASURE_TREE_NODES), 1)
        self.assertEqual(f.size(SizeOracle.MEASURE_DAG_NODES), 1)
        self.assertEqual(f.size(SizeOracle.MEASURE_LEAVES), 1)
        self.assertEqual(f.size(SizeOracle.MEASURE_DEPTH), 1)
        self.assertEqual(f.size(SizeOracle.MEASURE_SYMBOLS), 0)

    def test_basic(self):
        varA = Symbol("A")
        f = And(varA, Not(varA))

        self.assertEqual(f.size(), 4)
        self.assertEqual(f.size(SizeOracle.MEASURE_TREE_NODES), 4)
        self.assertEqual(f.size(SizeOracle.MEASURE_DAG_NODES), 3)
        self.assertEqual(varA.size(SizeOracle.MEASURE_LEAVES), 1)
        self.assertEqual(f.size(SizeOracle.MEASURE_DEPTH), 3)
        self.assertEqual(f.size(SizeOracle.MEASURE_SYMBOLS), 1)

    def test_bool_dag(self):
        p = Symbol("p", INT)
        x = Symbol("x")
        f = Or(x, GT(p, Int(0)), And(x, x))
        bool_dag = f.size(SizeOracle.MEASURE_BOOL_DAG)
        self.assertEqual(bool_dag, 4)

    def test_examples(self):
        for (f, _, _, _) in get_example_formulae():
            tree_size = f.size(SizeOracle.MEASURE_TREE_NODES)
            dag_size = f.size(SizeOracle.MEASURE_DAG_NODES)
            leaves = f.size(SizeOracle.MEASURE_LEAVES)
            depth = f.size(SizeOracle.MEASURE_DEPTH)
            symbols = f.size(SizeOracle.MEASURE_SYMBOLS)
            bool_dag = f.size(SizeOracle.MEASURE_BOOL_DAG)
            self.assertTrue(tree_size >= dag_size)
            self.assertTrue(dag_size >= depth)
            self.assertTrue(dag_size >= leaves)
            self.assertTrue(leaves >= symbols)
            self.assertTrue(dag_size >= bool_dag)

    def test_error(self):
        varA = Symbol("A")
        with self.assertRaises(NotImplementedError):
            varA.size("non-existent")


if __name__ == '__main__':
    main()
