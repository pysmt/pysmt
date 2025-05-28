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

from pysmt.rewritings import adt_to_euf
from pysmt.test import TestCase, main
from pysmt.typeguard import is_adt_constructor
from pysmt.typing import (
    REAL,
    AlgebraicDataType,
    BOOL,
    INT,
    ADSSelf,
    _AlgebraicDataType,
)
from pysmt.environment import get_env, reset_env


class TestDatatype(TestCase):

    def setUp(self):
        def assertFunctionIs(function, return_type, params_type):
            self.assertEqual(function.return_type, return_type)
            self.assertEqual(function.param_types, params_type)

        self.assertFunctionIs = assertFunctionIs

        self.tree = AlgebraicDataType(
            "tree", nil=(), leaf=(("val", INT),), node=(("left", ADSSelf), ("right", ADSSelf))
        )
        self.forest = AlgebraicDataType(
            "forest", nil=(), cons=(("hd", self.tree), ("tl", ADSSelf))
        )
        self.list = AlgebraicDataType(
            "list", nil=(), cons=(("hd", INT), ("tl", ADSSelf))
        )
        self.env = get_env()
        self.formula_mgr = self.env.formula_manager

        def cleanUpEnv():
            self.env = reset_env()
            self.formula_mgr = self.env.formula_manager

        self.addCleanup(cleanUpEnv)

    def __test_rewrite(self, rewrite, ground):
        self.assertTrue(
            rewrite == ground,
            "Test excpected output of the rewrite with the compute one\n"
            + "Computed: "
            + self.env.HRSerializerClass().serialize(rewrite)
            + "\n"
            + "Expected: "
            + self.env.HRSerializerClass().serialize(ground)
            + "\n",
        )

    def test_is_correct_type(self):
        self.assertTrue(isinstance(self.tree, _AlgebraicDataType))
        self.assertTrue(isinstance(self.forest, _AlgebraicDataType))
        self.assertTrue(self.tree.is_algebraic_data_type())
        self.assertTrue(self.forest.is_algebraic_data_type())

    def test_equality(self):
        dt_list_type = AlgebraicDataType(
            "list", nil=(), cons=(("hd", INT), ("tl", ADSSelf))
        )
        dt_list_type2 = AlgebraicDataType(
            "list", cons=(("hd", INT), ("tl", ADSSelf)), nil=()
        )
        self.assertEqual(dt_list_type, dt_list_type2)

    def test_constructors_type(self):
        self.assertTrue(self.tree.is_algebraic_data_type())
        self.assertTrue(self.forest.is_algebraic_data_type())

        self.assertFunctionIs(self.tree.leaf, self.tree, (INT,))
        self.assertFunctionIs(self.tree.node, self.tree, (self.tree, self.tree))

        self.assertFunctionIs(self.forest.nil, self.forest, ())
        self.assertFunctionIs(self.forest.cons, self.forest, (self.tree, self.forest))

    def test_selector_type(self):
        self.assertTrue(self.tree.is_algebraic_data_type())
        self.assertTrue(self.forest.is_algebraic_data_type())

        self.assertFunctionIs(self.tree.val, INT, (self.tree,))
        self.assertFunctionIs(self.tree.left, self.tree, (self.tree,))
        self.assertFunctionIs(self.tree.right, self.tree, (self.tree,))

        self.assertFunctionIs(self.forest.hd, self.tree, (self.forest,))
        self.assertFunctionIs(self.forest.tl, self.forest, (self.forest,))

    def test_discriminator_type(self):
        self.assertTrue(self.tree.is_algebraic_data_type())
        self.assertTrue(self.forest.is_algebraic_data_type())

        self.assertFunctionIs(self.tree.is_leaf, BOOL, (self.tree,))
        self.assertFunctionIs(self.tree.is_node, BOOL, (self.tree,))

        self.assertFunctionIs(self.forest.is_nil, BOOL, (self.forest,))
        self.assertFunctionIs(self.forest.is_cons, BOOL, (self.forest,))

    def test_rewrite_symbol_eq_constructor(self):
        f_mgr = self.formula_mgr

        rewrite = adt_to_euf(
            f_mgr.Equals(
                f_mgr.Symbol("t_leaf_1", self.tree),
                f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
            ),
            self.env,
        )

        if not is_adt_constructor(self.tree.leaf):
            assert False

        true_rewrite = f_mgr.And(
            f_mgr.And(
                f_mgr.Equals(
                    f_mgr.Symbol("t_leaf_1", self.tree),
                    f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                ),
                f_mgr.Discriminator(
                    self.tree.is_leaf, f_mgr.Symbol("t_leaf_1", self.tree)
                ),
                f_mgr.And(
                    *(
                        f_mgr.Equals(
                            f_mgr.Selector(
                                self.tree[param], f_mgr.Symbol("t_leaf_1", self.tree)
                            ),
                            val,
                        )
                        for (param, _), val in zip(
                            self.tree.leaf.parameters,
                            (f_mgr.Int(1),),
                        )
                    )
                ),
            ),
            f_mgr.Or(
                f_mgr.And(
                    f_mgr.Discriminator(
                        self.tree["is_leaf"], f_mgr.Symbol("t_leaf_1", self.tree)
                    ),
                    f_mgr.Not(
                        f_mgr.Discriminator(
                            self.tree["is_node"], f_mgr.Symbol("t_leaf_1", self.tree)
                        ),
                    ),
                ),
                f_mgr.And(
                    f_mgr.Not(
                        f_mgr.Discriminator(
                            self.tree["is_leaf"], f_mgr.Symbol("t_leaf_1", self.tree)
                        )
                    ),
                    f_mgr.Discriminator(
                        self.tree["is_node"], f_mgr.Symbol("t_leaf_1", self.tree)
                    ),
                ),
            ),
        )
        # self.__test_rewrite(rewrite, true_rewrite)

        rewrite = adt_to_euf(
            f_mgr.Equals(
                f_mgr.Symbol("t_list_1_nil", self.list),
                f_mgr.Constructor(
                    self.list.cons, f_mgr.Int(1), f_mgr.Constructor(self.list.nil)
                ),
            ),
            self.env,
        )

        if not is_adt_constructor(self.list.cons):
            assert False

        true_rewrite = f_mgr.And(
            f_mgr.And(
                f_mgr.Equals(
                    f_mgr.Symbol("t_list_1_nil", self.list),
                    f_mgr.Constructor(
                        self.list.cons, f_mgr.Int(1), f_mgr.Constructor(self.list.nil)
                    ),
                ),
                f_mgr.Discriminator(
                    self.list["is_cons"], f_mgr.Symbol("t_list_1_nil", self.list)
                ),
                f_mgr.And(
                    *(
                        f_mgr.Equals(
                            f_mgr.Selector(
                                self.list[param],
                                f_mgr.Symbol("t_list_1_nil", self.list),
                            ),
                            val,
                        )
                        for (param, _), val in zip(
                            self.list.cons.parameters,
                            (f_mgr.Int(1), f_mgr.Constructor(self.list.nil)),
                        )
                    )
                ),
            ),
            f_mgr.Or(
                f_mgr.And(
                    f_mgr.Discriminator(
                        self.list.is_cons, f_mgr.Symbol("t_list_1_nil", self.list)
                    ),
                    f_mgr.Not(
                        f_mgr.Discriminator(
                            self.list.is_nil,
                            f_mgr.Symbol("t_list_1_nil", self.list),
                        ),
                    ),
                ),
                f_mgr.And(
                    f_mgr.Not(
                        f_mgr.Discriminator(
                            self.list.is_cons,
                            f_mgr.Symbol("t_list_1_nil", self.list),
                        )
                    ),
                    f_mgr.Discriminator(
                        self.list.is_nil, f_mgr.Symbol("t_list_1_nil", self.list)
                    ),
                ),
            ),
            f_mgr.Iff(
                f_mgr.Discriminator(
                    self.list.is_nil, f_mgr.Symbol("t_list_1_nil", self.list)
                ),
                f_mgr.Equals(
                    f_mgr.Constructor(self.list.nil),
                    f_mgr.Symbol("t_list_1_nil", self.list),
                ),
            ),
        )

        # self.__test_rewrite(rewrite, true_rewrite)

    def test_rewrite_symbol_eq_selector(self):
        f_mgr = self.formula_mgr
        t_mgr = self.env.type_manager

        # Testing with a leaf
        rewrite = adt_to_euf(
            f_mgr.Equals(
                f_mgr.Selector(self.tree.val, f_mgr.Symbol("t_leaf_1", self.tree)),
                f_mgr.Int(1),
            ),
            self.env,
        )

        true_rewrite = f_mgr.And()

        # self.__test_rewrite(rewrite, true_rewrite)

        # Testing with a list
        rewrite = adt_to_euf(
            f_mgr.Equals(
                f_mgr.Int(1),
                f_mgr.Selector(self.list.hd, f_mgr.Symbol("t_list_1_nil", self.list)),
            ),
            self.env,
        )

        true_rewrite = f_mgr.And()

        # self.__test_rewrite(rewrite, true_rewrite)

    def test_constructor_eq(self):
        f_mgr = self.formula_mgr

        rewrite = adt_to_euf(
            f_mgr.And(
                f_mgr.Equals(
                    f_mgr.Symbol("t_leaf_1", self.tree),
                    f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                ),
                f_mgr.Equals(
                    f_mgr.Constructor(
                        self.tree.node,
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(2)),
                    ),
                    f_mgr.Symbol("t_leaf_1", self.tree),
                ),
            ),
            self.env,
        )

        self.assertUnsat(rewrite, solver_name="msat")

        rewrite = adt_to_euf(
            f_mgr.And(
                f_mgr.Equals(
                    f_mgr.Symbol("t_leaf_1", self.tree),
                    f_mgr.Constructor(
                        self.tree.node,
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(2)),
                    ),
                ),
                f_mgr.Equals(
                    f_mgr.Constructor(
                        self.tree.node,
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(2)),
                    ),
                    f_mgr.Symbol("t_leaf_1", self.tree),
                ),
            ),
            self.env,
        )

        self.assertSat(rewrite, solver_name="msat")

        first = (
            f_mgr.Equals(
                f_mgr.Constructor(
                    self.tree.node,
                    f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                    f_mgr.Constructor(
                        self.tree.node,
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(2)),
                        f_mgr.Constructor(
                            self.tree.node,
                            f_mgr.Constructor(self.tree.leaf, f_mgr.Int(3)),
                            f_mgr.Constructor(self.tree.nil),
                        ),
                    ),
                ),
                f_mgr.Symbol("tree_1_2_3_r", self.tree),
            )
        )

        second =(
            f_mgr.Equals(
                f_mgr.Constructor(
                    self.tree.node,
                    f_mgr.Constructor(
                        self.tree.node,
                        f_mgr.Constructor(
                            self.tree.node,
                            f_mgr.Constructor(self.tree.nil),
                            f_mgr.Constructor(self.tree.leaf, f_mgr.Int(3)),
                        ),
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(2)),
                    ),
                    f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                ),
                f_mgr.Symbol("tree_1_2_3_l", self.tree),
            )
        )

        eq_sub_tree = (
            f_mgr.Equals(
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.left,
                        f_mgr.Selector(
                            self.tree.right,
                            f_mgr.Selector(
                                self.tree.right,
                                f_mgr.Selector(
                                    self.tree.right,
                                    f_mgr.Symbol("tree_1_2_3_r", self.tree),
                                ),
                            ),
                        ),
                    ),
                ),
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.right,
                        f_mgr.Selector(
                            self.tree.left,
                            f_mgr.Selector(
                                self.tree.left,
                                f_mgr.Selector(
                                    self.tree.left,
                                    f_mgr.Symbol("tree_1_2_3_l", self.tree),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            f_mgr.Equals(
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.left,
                        f_mgr.Selector(
                            self.tree.right,
                            f_mgr.Selector(
                                self.tree.right,
                                f_mgr.Symbol("tree_1_2_3_r", self.tree),
                            ),
                        ),
                    ),
                ),
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.right,
                        f_mgr.Selector(
                            self.tree.left,
                            f_mgr.Selector(
                                self.tree.left,
                                f_mgr.Symbol("tree_1_2_3_l", self.tree),
                            ),
                        ),
                    ),
                ),
            ),
            f_mgr.Equals(
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.left,
                        f_mgr.Selector(
                            self.tree.right, f_mgr.Symbol("tree_1_2_3_r", self.tree)
                        ),
                    ),
                ),
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.right,
                        f_mgr.Selector(
                            self.tree.left, f_mgr.Symbol("tree_1_2_3_l", self.tree)
                        ),
                    ),
                ),
            ),
            f_mgr.Equals(
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.left, f_mgr.Symbol("tree_1_2_3_r", self.tree)
                    ),
                ),
                f_mgr.Selector(
                    self.tree.val,
                    f_mgr.Selector(
                        self.tree.right, f_mgr.Symbol("tree_1_2_3_l", self.tree)
                    ),
                ),
            ),
        )


        rewrite = adt_to_euf(
            f_mgr.And(
                *eq_sub_tree,
                first,
                second,
            )
        )

        print(self.env.HRSerializerClass().serialize(rewrite).replace('=','==').replace('is-','is_').replace('!','not').replace('<->','**').replace('->','*'))

        self.assertSat(
            rewrite,
            solver_name="msat",
        )



    def test_symbol_creation(self):
        f_mgr = self.formula_mgr
        leaf_1 = f_mgr.Symbol("leaf_1", self.tree)
        leaf_2 = f_mgr.Symbol("leaf_2", self.tree)

        eq_1 = f_mgr.Equals(f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)), leaf_1)
        eq_2 = f_mgr.Equals(f_mgr.Constructor(self.tree.leaf, f_mgr.Int(2)), leaf_2)

        eq_3 = f_mgr.And(eq_1, eq_2, f_mgr.Equals(leaf_1, leaf_2))

        # self.assertUnsat(eq_3, solver_name="msat")
        # self.assertValid(eq_3, solver_name="mathsat")

    def test_flattening(self):
        f_mgr = self.formula_mgr
        rewrite = adt_to_euf(
            f_mgr.Equals(
                f_mgr.Constructor(
                    self.tree.node,
                    f_mgr.Constructor(self.tree.leaf, f_mgr.Int(1)),
                    f_mgr.Constructor(
                        self.tree.node,
                        f_mgr.Constructor(self.tree.leaf, f_mgr.Int(2)),
                        f_mgr.Constructor(
                            self.tree.node,
                            f_mgr.Constructor(self.tree.leaf, f_mgr.Int(3)),
                            f_mgr.Constructor(self.tree.nil),
                        ),
                    ),
                ),
                f_mgr.Symbol("t_leaf_1", self.tree),
            )
        )

    def test_acyclics(self):
        f_mgr = self.formula_mgr

        rewrite = adt_to_euf(
            f_mgr.And(
                *(
                    f_mgr.Equals(
                        f_mgr.Symbol(f"x_{k}", self.list),
                        f_mgr.Selector(
                            self.list.tl,
                            f_mgr.Symbol(f"x_{(k + 1) % 10}", self.list),
                        )
                    )
                    for k in range(10)
                )
            ),
            self.env,
        )

        print(
            self.env.HRSerializerClass()
            .serialize(rewrite)
            .replace("=", "==")
            .replace("is-", "is_")
            .replace("!", "not")
            .replace("<->", "**")
            .replace("->", "*")
        )

        self.assertUnsat(
            rewrite,
            solver_name="msat",
        )


if __name__ == "__main__":
    main()
