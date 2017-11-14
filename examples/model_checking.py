# This example shows a more advance use of pySMT.
#
# It provides a simple implementation of Bounded Model Checking [1]
# with K-Induction [2], and PDR [3], and applies it on a simple 
# transition system.
#
# [1] ...
#
# [2] ...
#
# [3] ...
#
from six.moves import xrange

from pysmt.shortcuts import Symbol, Not, And, Or, EqualsOrIff, Implies
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL

def next_var(v):
    """Returns the 'next' of the given variable"""
    return Symbol("next(%s)" % v.symbol_name(), v.symbol_type())

def at_time(v, t):
    """Builds an SMT variable representing v at time t"""
    return Symbol("%s@%d" % (v.symbol_name(), t), v.symbol_type())


class TransitionSystem(object):
    """Trivial representation of a Transition System."""

    def __init__(self, variables, init, trans):
        self.variables = variables
        self.init = init
        self.trans = trans

# EOC TransitionSystem


class PDR(object):
    def __init__(self, system):
        self.system = system
        self.R = [system.init]
        self.solver = Solver()
        
    def check_property(self, prop):
        """Property Directed Reachability approach without optimizations."""
        print("Checking property %s..." % prop)

        while True:
            cube = self.get_bad_state(prop)
            if cube is not None:
                if self.recursive_block(cube):
                    print("--> Bug found at step %d" % (len(self.R)))
                    return
            else:
                if self.inductive(prop):
                    print("--> The system is safe!")
                    return
                print("   [PDR]    Adding frame %d..." % (len(self.R)))
                self.R.append(TRUE())

    def get_bad_state(self, prop):
        """Extracts a reachable state that intersects the negation 
        of the property and the last current frame"""
        return self.solve(And(self.R[-1], Not(prop)))

    def solve(self, formula):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        self.solver.reset_assertions()
        self.solver.add_assertion(formula)
        if self.solver.solve():
            return And([EqualsOrIff(v, self.solver.get_value(v)) for v in self.system.variables])
        return None

    def recursive_block(self, cube):
        """Blocks the cube at each frame, if possible."""
        for i in range(len(self.R)-1, 0, -1):
            cubeprime = cube.substitute(dict([(v, next_var(v)) for v in self.system.variables]))
            cubepre = self.solve(And(self.R[i-1], self.system.trans, Not(cube), cubeprime))
            if cubepre is None:
                for j in range(1, i+1):
                    self.R[j] = And(self.R[j], Not(cube))
                return False
            cube = cubepre
        return True
    
    def inductive(self, prop):
        """Checks if last two frames are equivalent """
        if len(self.R) > 1 and \
           self.solve(Not(EqualsOrIff(self.R[-1], self.R[-2]))) is None:
            return True
        return False
        
class BMCInduction(object):
    
    def __init__(self, system):
        self.system = system
    
    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
        subs_i = {}
        for v in self.system.variables:
            subs_i[v] = at_time(v, i)
            subs_i[next_var(v)] = at_time(v, i+1)
        return subs_i


    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:

        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
        """
        res = []
        for i in xrange(k+1):
            subs_i = self.get_subs(i)
            res.append(self.system.trans.substitute(subs_i))
        return And(res)


    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        each time encodes a different state
        """
        res = []
        for i in xrange(k+1):
            subs_i = self.get_subs(i)
            for j in xrange(i+1, k+1):
                state = []
                subs_j = self.get_subs(j)
                for v in self.system.variables:
                    v_i = v.substitute(subs_i)
                    v_j = v.substitute(subs_j)
                    state.append(Not(EqualsOrIff(v_i, v_j)))
                res.append(Or(state))
        return And(res)


    def get_k_hypothesis(self, prop, k):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property"""
        res = []
        for i in xrange(k):
            subs_i = self.get_subs(i)
            res.append(prop.substitute(subs_i))
        return And(res)


    def get_bmc(self, prop, k):
        """Returns the BMC encoding at step k"""
        init_0 = self.system.init.substitute(self.get_subs(0))
        prop_k = prop.substitute(self.get_subs(k))
        return And(self.get_unrolling(k), init_0, Not(prop_k))

    def get_k_induction(self, prop, k):
        """Returns the K-Induction encoding at step K"""
        subs_k = self.get_subs(k)
        prop_k = prop.substitute(subs_k)
        return And(self.get_unrolling(k),
                   self.get_k_hypothesis(prop, k),
                   self.get_simple_path(k),
                   Not(prop_k))

    def check_property(self, prop):
        """Interleaves BMC and K-Ind to verify the property."""
        print("Checking property %s..." % prop)
        for b in xrange(100):
            f = self.get_bmc(prop, b)
            print("   [BMC]    Checking bound %d..." % (b+1))
            if is_sat(f):
                print("--> Bug found at step %d" % (b+1))
                return

            f = self.get_k_induction(prop, b)
            print("   [K-IND]  Checking bound %d..." % (b+1))
            if is_unsat(f):
                print("--> The system is safe!")
                return


def counter(bit_count):
    """Counter example with n bits and reset signal."""

    # Example Counter System (SMV-like syntax)
    #
    # VAR bits: word[bit_count];
    #     reset: boolean;
    #
    # INIT: bits = 0 & reset = FALSE;
    #
    # TRANS: next(bits) = bits + 1;
    # TRANS: next(reset) = (next(bits) = 0 -> next(reset)) & (bits != 0 -> !reset);
    
    bits = [Symbol("b%s"%b, BOOL) for b in range(bit_count)]
    bits.reverse()
    nbits = [next_var(x) for x in bits]
    reset = Symbol("r", BOOL)
    nreset = next_var(reset)
    variables = bits + [reset]

    count = []    
    tr = []
    get_bin = lambda x, n: format(x, 'b').zfill(n)
    conv = lambda v, x: v if x == 1 else Not(v)
    
    for idx in range((2**bit_count)-1):
        val = [int(x) for x in str(get_bin(idx, bit_count))]
        for j in range(len(val)):
            val[j] = conv(bits[j], val[j])
        val1 = [int(x) for x in str(get_bin(idx+1, bit_count))]
        for j in range(len(val1)):
            val1[j] = conv(nbits[j], val1[j])
        tr.append(And(val + val1))

    tr.append(And(And(bits), And([Not(b) for b in nbits])))
    
    count_trans = Or(tr)
    reset_trans = And(EqualsOrIff(And(bits), nreset), Implies(reset, Not(nreset)))
    trans = And(count_trans, reset_trans)

    init = And([Not(b) for b in bits]+[Not(reset)])

    # A true invariant property: (reset -> bits = 0) & (bits != 0 -> !reset)
    true_prop = And(Implies(reset, And([Not(b) for b in bits])), Implies(Or(bits), Not(reset)))

    # A false invariant property: (bits != 2**bit_count)
    false_prop = Not(And(bits))

    return (TransitionSystem(variables, init, trans), [true_prop, false_prop])
            
def main():
    example = counter(4)
    
    bmcind = BMCInduction(example[0])
    pdr = PDR(example[0])
    
    for prop in example[1]:
        bmcind.check_property(prop)
        pdr.check_property(prop)
        print("")

if __name__ == "__main__":
    main()
