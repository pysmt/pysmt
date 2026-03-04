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
import warnings

import pysmt.walkers
from pysmt.walkers.generic import handles
import pysmt.operators as op
from pysmt.exceptions import PysmtTypeError, PysmtValueError



class FunctionInterpretation:
    """This class represents the interpretation of an uninterpreted
    function symbol and is intended to be used in substitutions.

    For example, let `phi` be the formula `phi = Equals(Function(f,
    [Int(2), Int(3)]), a)` where `a` is a Symbol of type INT and `f`
    is an uninterpreted function with two INT parameters that returns
    INT. A possible interpretation for `f` could be `f(x, y) = x + y`
    and a model for `a` could be `5`.

    To represent a model in pysmt we simply use a dict from symbols to
    constant values, but for interpretations we need a map from
    symbols to instances of FunctionInterpretation. Each instance of
    FunctionInterpretation represents the interpretation of a
    function.

    A FunctionInterpretation is represented as a list of symbols, each
    having the type corresponding to the parameter typres of the
    function to be interpreted, plus a function body that is an
    expression that can only depend on the formal parameters. So to
    represent the interpretation `f(x, y) = x + y` we construct the
    instance as follows:

    ```
    x, y = Symbol('x', INT), Symbol('y', INT)
    FunctionInterpretation([x, y], Plus(x, y))
    ```
    """

    def __init__(self, formal_params, function_body, allow_free_vars=False):
        """Constructor, taking in input the list of formal parameters and the
        function body.

        The parameter `allow_free_vars` is used to skip the check that
        the function body has no free variables other than formal
        parameter and is used in the SmtLib model-validation utility
        because functions with uninterpreted return value return
        special symbols (e.g. @val1) in SmtLib.
        """
        if any(not x.is_symbol() or not x.is_term() for x in formal_params):
            raise PysmtValueError('Formal parameters of a function '
                                  'interpretation must be non-function symbols')
        if not allow_free_vars and \
           not function_body.get_free_variables().issubset(set(formal_params)):
            raise PysmtValueError('the body of a function interpretation cannot'
                                  ' contain free variables other than formal '
                                  'parameters')
        self.formal_params = list(formal_params)
        self.function_body = function_body


    def interpret(self, env, actual_params):
        """Given a set of actual parameter, returns the 'value' of the
        function by substitutiong formal parameters with their actual
        values.
        """
        if len(actual_params) !=  len(self.formal_params):
            raise ValueError('The numbe of actual parameters does not match '
                             'with the number of formal parameters')
        subs = dict(zip(self.formal_params, actual_params))
        SubsClass = type(env.substituter)
        return SubsClass(env).substitute(self.function_body, subs)



class Substituter(pysmt.walkers.IdentityDagWalker):
    """Performs substitution of a set of terms within a formula.

    Let f be a formula ans subs be a map from formula to formula.
    Substitution returns a formula f' in which all occurrences of the
    keys of the map have been replaced by their value.

    There are a few considerations to take into account:
      - In which order to apply the substitution
      - How to deal with quantified subformulas

    The order in which we apply the substitutions gives raise to two
    different approaches: Most General Substitution and Most Specific
    Substitution. Lets consider the example:

      f = (a & b)
      subs = {a -> c, (c & b) -> d, (a & b) -> c}

    With the Most General Substitution (MGS) we obtain:
      f' = c
    with the Most Specific Substitution (MSS) we obtain:
      f' = d

    The default behavior before version 0.5 was MSS. However, this
    leads to unexpected results when dealing with literals, i.e.,
    substitutions in which both x and Not(x) appear, do not work as
    expected.  In case of doubt, it is recommended to issue two
    separate calls to the substitution procedure.
    """
    def __init__(self, env):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=env, invalidate_memoization=True)
        self.manager = self.env.formula_manager
        if self.__class__ == Substituter:
            raise NotImplementedError(
                "Cannot instantiate abstract Substituter class directly. "
                "Use MSSubstituter or MGSubstituter instead.")

    def _get_key(self, formula, **kwargs):
        return formula

    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""

        # Deal with quantifiers
        if formula.is_quantifier():
            # 1. We create a new substitution in which we remove the
            #    bound variables from the substitution map
            substitutions = kwargs["substitutions"]
            new_subs = {}
            for k,v in substitutions.items():
                # If at least one bound variable is in the cone of k,
                # we do not consider this substitution in the body of
                # the quantifier.
                if all(m not in formula.quantifier_vars()
                       for m in k.get_free_variables()):
                    new_subs[k] = v

            # 2. We apply the substitution on the quantifier body with
            #    the new 'reduced' map
            sub = self.__class__(self.env)
            res_formula = sub.substitute(formula.arg(0), new_subs)

            # 3. We invoke the relevant function (walk_exists or
            #    walk_forall) to compute the substitution
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=[res_formula], **kwargs)

            # 4. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            pysmt.walkers.IdentityDagWalker._push_with_children_to_stack(self,
                                                                         formula,
                                                                         **kwargs)

    def substitute(self, formula, subs=None, interpretations=None):
        """Replaces any subformula in formula with the definition in subs (if
        any) and interprets function symbols with the interpretations
        in `interpretations`

        For example, let `phi` be the formula `phi = Equals(Function(f,
        [Int(2), Int(3)]), Plus(a, Int(1)))` where `a` is a Symbol of type INT and `f`
        is an uninterpreted function with two INT parameters that returns
        INT.

        Examples:

        - Basic substitution:
        `self.substitute(phi, {a: Int(5)})`
        will give `Equals(Function(f, [Int(2), Int(3)]), Plus(Int(5), Int(1)))`

        - Interpretation:
        ```
        x, y = Symbol('x', INT), Symbol('y', INT)
        i = FunctionInterpretation([x, y], Plus(x, y))
        self.substitute(phi, interpretations={f:i})
        ```
        will give `Equals(Int(5), Plus(a, Int(1)))`

        - Term substitution
        `self.substitute(phi, {Plus(a, Int(1)): Int(5)})`
        will give `Equals(Function(f, [Int(2), Int(3)]), Int(6))`
        """

        # Check that formula is a term
        if not formula.is_term():
            raise PysmtTypeError("substitute() can only be used on terms.")

        if subs is None:
            subs = {}
        if interpretations is None:
            interpretations = {}

        for i, (k, v) in enumerate(subs.items()):
            # Check that substitutions are terms
            if not k.is_term():
                raise PysmtTypeError(
                    "Only terms should be provided as substitutions." +
                    " Non-term '%s' found." % k)
            if not v.is_term():
                raise PysmtTypeError(
                    "Only terms should be provided as substitutions." +
                    " Non-term '%s' found." % v)
            # Check that substitutions belong to the current formula manager
            if k not in self.manager:
                raise PysmtTypeError(
                    "Key %d does not belong to the Formula Manager." % i)
            if v not in self.manager:
                raise PysmtTypeError(
                    "Value %d does not belong to the Formula Manager." % i)

        for i, (k, v) in enumerate(interpretations.items()):
            # Check that interpretations are terms
            if not k.is_symbol() or k.is_term():
                raise PysmtTypeError(
                    "Only function symbols should be provided as interpretation"
                    " keys. Non-function '%s' found." % k)
            if not isinstance(v, FunctionInterpretation):
                raise PysmtTypeError(
                    "Only FunctionInterpretation objects should be provided as "
                    "interpretation values. Object '%s' of type %s "
                    "found." % (v, type(v)))
            # Check that interpretations belong to the current formula manager
            if k not in self.manager:
                raise PysmtTypeError(
                    "Key %d does not belong to the Formula Manager." % i)

        res = self.walk(formula, substitutions=subs,
                        interpretations=interpretations)
        return res

    def walk_function(self, formula, args, **kwargs):
        f = formula.function_name()
        interpretations = kwargs['interpretations']
        if f in interpretations:
            res = interpretations[f].interpret(self.env, args)
        else:
            res = pysmt.walkers.IdentityDagWalker.super(self, formula,
                                                        args=args, **kwargs)
        return res


class MGSubstituter(Substituter):
    """Performs Most Generic Substitution.

    This is the default behavior since version 0.5
    """
    def __init__(self, env):
        Substituter.__init__(self, env=env)

    @handles(set(op.ALL_TYPES) - op.QUANTIFIERS - {op.FUNCTION})
    def walk_identity_or_replace(self, formula, args, **kwargs):
        """
        If the formula appears in the substitution, return the substitution.
        Otherwise, rebuild the formula by calling the IdentityWalker.
        """
        substitutions = kwargs['substitutions']
        res = substitutions.get(formula, None)
        if res is None:
            res = Substituter.super(self, formula, args=args, **kwargs)
        return res

    def walk_forall(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        res = substitutions.get(formula, None)
        if res is None:
            qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
            res = self.mgr.ForAll(qvars, args[0])
        return res

    def walk_exists(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        res = substitutions.get(formula, None)
        if res is None:
            qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
            res = self.mgr.Exists(qvars, args[0])
        return res


# EOC MGSubstituter


class MSSubstituter(Substituter):
    """Performs Most Specific Substitution.

    This was the default beahvior before version 0.5
    """

    def __init__(self, env):
        Substituter.__init__(self, env=env)

    def substitute(self, formula, subs):
        return Substituter.substitute(self, formula, subs)

    def _substitute(self, formula, substitutions):
        """Returns the substitution for formula, if one is defined, otherwise
        returns the formula unchanged.

        This is an helper function, to simplify the implementation of
        the walk_* functions.
        """
        return substitutions.get(formula, formula)

    @handles(set(op.ALL_TYPES) - op.QUANTIFIERS - {op.FUNCTION})
    def walk_replace(self, formula, args, **kwargs):
        new_f =  Substituter.super(self, formula, args=args, **kwargs)
        return self._substitute(new_f, kwargs['substitutions'])

    def walk_forall(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        new_f = self.mgr.ForAll(qvars, args[0])
        return self._substitute(new_f, substitutions)

    def walk_exists(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        new_f = self.mgr.Exists(qvars, args[0])
        return self._substitute(new_f, substitutions)

# EOC MSSSubstituter
