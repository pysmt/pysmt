.. _pysmt-tutorials-booleanlogic:

Boolean Logic with PySMT
========================

This tutorial will guide you through the basic features of PySMT!

Basic Solving
-------------

PySMT is a library that simplifies the use of modern Satisfiability
Modulo Theory technology.

In this first demo, we will introduce basic solving, that is how to
create a simple logical formula, with variables, how to check if a model
for such a formula exists and, if it does, how to retrieve a satisfying
assignemnt for the variables.

As for any python library, the very first step is to import the
functions and classes we need for our application. PySMT is designed to
be highly structured and reentrant, but offers a simplified API that
serves most of the classical usage of an SMT solver. Such API groups in
a single module all the functions to construct formulae, to check the
satisfiability and to retrieve Solver instances.

The module to import is ``pysmt.shortcuts``.

In our example, we need six functions: ``Symbol``, ``And``,
``Not``, ``Or``, ``is_sat`` and ``get_model``.

.. code:: python

    from pysmt.shortcuts import Symbol, And, Not, Or, is_sat, get_model

The first formula we want to check in this example is the classic
unsatisfiable formula: :math:`a \wedge \neg a`

For this purpose, we first need to create a new variable :math:`a`.
PySMT variables are called "symbols" and are created using the
``Symbol`` shortcut. The function takes in input a variable name and
optionally a type that will be useful when we'll introduce SMT theories.
By default, the symbols are Booleans, hence the following code creates
and returns the PySMT representation for a variable :math:`a`.

.. code:: python

    a = Symbol("a")

At this point, we can create our formula. PySMT offers a number of
functions to construct formulae like conjunction (``And``), disjunction
(``Or``), negation (``Not``) and so on. Each builds a PySMT
representation of a formula given as arguments other formulae. For
example, ``Not(a)`` returns the PySMT representation of :math:`\neg a`.
We can build the formula :math:`a \wedge \neg a` as follows.

.. code:: python

    phi = And(a, Not(a))

Each formula in PySMT can be easily printed or converted to a
human-readble string. Very large formulae are not printed completely by
default, but the ``serialize`` method allows to get the full
serialization.

.. code:: python

    print(phi)
    string_repr = str(phi)
    serialized_strinf = phi.serialize()


.. parsed-literal::

    (a & (! a))


Given a first order formula, checking its satisfiability means checking
if there exists an interpretation for its non-logical symbols that makes
the formula true. Our example is actually a propositional formula, and
checking satisfiability amounts to check if there is a truth value for
the variables appearing in the formula that makes the formula true.

Clearly, our example formula is not satisfiable (it is UNSAT), because
assigning :math:`a = \top` makes the formula false as assigning
:math:`a = \bot`.

The basic goal of PySMT is to provide you the possibility of quickly and
simply checking satisfiability of formulae. The ``is_sat`` function is
the simpler way of checking the satisfiability of any given formula. It
takes a formula and returns ``True`` if it is satisfiable, otherwise it
returns ``False``.

.. code:: python

    check = is_sat(phi)
    assert check is False

Now, to show what happens with a satisfiable formula, we create the
representation for :math:`(a \wedge \neg a) \vee b`. This formula is
clearly satisfiable, because assigning :math:`b = \top` is sufficient to
make the formula true.

.. code:: python

    b = Symbol("b")
    psi = Or(phi, b)

At this point, we can check that the formula is satisfiable. We could
use again the ``is_sat`` function, but this time we'll show another
useful shortcut that provides information about the satisfiability, but
also creates and returns a satisfying model for the formula.

This function is called ``get_model`` and given a formula, it returns
``None`` if the formula is UNSAT, otherwise it returns an object
implementing the ``Model`` interface, that can be queried to retrive a
satisfying assignment. We shall see the ``Model`` interface in detail,
but for now we will use some basic features.

.. code:: python

    m = get_model(psi)
    assert m is not None

Given a model ``m``, we can retrive the python value for a variable
using the ``get_py_value`` method. The method takes in input any PySMT
formula and constructs a python representation for the value of the term
in the model.

In our example, the variable :math:`b` must be set to true to make the
formula true, hence the python value of the variable ``b`` must be
``True``.

.. code:: python

    assert m.get_py_value(b)
