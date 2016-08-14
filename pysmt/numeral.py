use_z3 = False
try:
    import z3num
    use_z3 = True
except:
    pass

if use_z3:
    class Numeral(z3num.Numeral):
        """Represents a Number (Algebraic)"""
        def __hash__(self):
            return hash(self.sexpr())

else:
    class Numeral(object):
        """Represents a Number (Algebraic)"""
        def __init__(self, obj):
            raise NotImplementedError("Z3 is not installed. "\
                "We currently do not support stand-alone algebraic numbers.")
