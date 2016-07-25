from pysmt.walkers import IdentityDagWalker


class Encoder(IdentityDagWalker):
    """Rewrites a formula in order to encode information for the solver.

    Encoder provides two methods:
     * encode(formula): returns a formula

    For an example of Encoder see EnumEncoder
    """
    def __init__(self, environment):
        IdentityDagWalker.__init__(self, environment)

    def encode(self, formula):
        """Returns a formula with the necessary information encoded."""
        # MG: Is this necessarily equisat?
        raise NotImplementedError

# EOC Encoder


class BoolUFEncoder(Encoder):
    """Rewrites an expression containing UF with boolean arguments into an
       equivalent one with only theory UF.

    This is needed because MathSAT does not support UF with boolean
    arguments.
    """

    def __init__(self, environment):
        Encoder.__init__(self, environment)
        self.get_type = self.env.stc.get_type
        self.mgr = self.env.formula_manager

    def encode(self, formula):
        return self.walk(formula)

    def walk_function(self, formula, args, **kwargs):
        from pysmt.typing import FunctionType
        # Separate arguments
        bool_args = []
        other_args = []
        for a in args:
            if self.get_type(a).is_bool_type():
                bool_args.append(a)
            else:
                other_args.append(a)

        if len(bool_args) == 0:
            # If no Bool Args, return as-is
            return IdentityDagWalker.walk_function(self, formula, args, **kwargs)

        # Build new function type
        rtype = formula.function_name().symbol_type().return_type
        ptype = [self.get_type(a) for a in other_args]
        if len(ptype) == 0:
            ftype = rtype
        else:
            ftype = FunctionType(rtype, ptype)

        # Base-case
        stack = []
        for i in xrange(2**len(bool_args)):
            fname = self.mgr.Symbol("%s#%i" % (formula.function_name(),i), ftype)
            if len(ptype) == 0:
                stack.append(fname)
            else:
                stack.append(self.mgr.Function(fname, tuple(other_args)))

        # Recursive case
        for b in bool_args:
            tmp = []
            while len(stack) > 0:
                lhs = stack.pop()
                rhs = stack.pop()
                # Simplify branches, if b is a constant
                if b.is_true():
                    tmp.append(lhs)
                elif b.is_false():
                    tmp.append(rhs)
                else:
                    ite = self.mgr.Ite(b, lhs, rhs)
                    tmp.append(ite)
            stack = tmp
        res = stack[0]
        return res
