# This example shows a more advance use of pySMT.
#
# It provides a simple implementation of Bounded Model Checking [1]
# with K-Induction [2], and PDR [3,4], and applies it on a simple
# transition system.
#
# [1] Biere, Cimatti, Clarke, Zhu,
#     "Symbolic Model Checking without BDDs",
#     TACAS 1999
#
# [2] Sheeran, Singh,  Stalmarck,
#     "Checking  safety  properties  using  induction  and  a SAT-solver",
#     FMCAD 2000
#
# [3] Bradley
#     "SAT-Based Model Checking without Unrolling",
#     VMCAI 2011
#
# [4] Een, Mischenko, Brayton
#     "Efficient implementation of property directed reachability",
#     FMCAD 2011
#
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
        self.frames = [system.init]
        self.solver = Solver()
        self.prime_map = dict([(v, next_var(v)) for v in self.system.variables])

    def check_property(self, prop):
        """Property Directed Reachability approach without optimizations."""
        print("Checking property %s..." % prop)

        while True:
            cube = self.get_bad_state(prop)
            if cube is not None:
                # Blocking phase of a bad state
                if self.recursive_block(cube):
                    print("--> Bug found at step %d" % (len(self.frames)))
                    break
                else:
                    print("   [PDR] Cube blocked '%s'" % str(cube))
            else:
                # Checking if the last two frames are equivalent i.e., are inductive
                if self.inductive():
                    print("--> The system is safe!")
                    break
                else:
                    print("   [PDR] Adding frame %d..." % (len(self.frames)))
                    self.frames.append(TRUE())

    def get_bad_state(self, prop):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        return self.solve(And(self.frames[-1], Not(prop)))

    def solve(self, formula):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        if self.solver.solve([formula]):
            return And([EqualsOrIff(v, self.solver.get_value(v)) for v in self.system.variables])
        return None

    def recursive_block(self, cube):
        """Blocks the cube at each frame, if possible.

        Returns True if the cube cannot be blocked.
        """
        for i in range(len(self.frames)-1, 0, -1):
            cubeprime = cube.substitute(dict([(v, next_var(v)) for v in self.system.variables]))
            cubepre = self.solve(And(self.frames[i-1], self.system.trans, Not(cube), cubeprime))
            if cubepre is None:
                for j in range(1, i+1):
                    self.frames[j] = And(self.frames[j], Not(cube))
                return False
            cube = cubepre
        return True

    def inductive(self):
        """Checks if last two frames are equivalent """
        if len(self.frames) > 1 and \
           self.solve(Not(EqualsOrIff(self.frames[-1], self.frames[-2]))) is None:
            return True
        return False

    def __del__(self):
        self.solver.exit()


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
        for i in range(k+1):
            subs_i = self.get_subs(i)
            res.append(self.system.trans.substitute(subs_i))
        return And(res)

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        each time encodes a different state
        """
        res = []
        for i in range(k+1):
            subs_i = self.get_subs(i)
            for j in range(i+1, k+1):
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
        for i in range(k):
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
        for b in range(100):
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
    # TRANS: next(bits) = bits + 1
    # TRANS: next(bits = 0) <-> next(reset)

    from pysmt.typing import BVType
    bits = Symbol("bits", BVType(bit_count))
    nbits = next_var(bits)
    reset = Symbol("r", BOOL)
    nreset = next_var(reset)
    variables = [bits, reset]

    init = bits.Equals(0) & Not(reset)

    trans = nbits.Equals(bits + 1) &\
            (nbits.Equals(0)).Iff(nreset)

    # A true invariant property: (reset -> bits = 0)
    true_prop = reset.Implies(bits.Equals(0))

    # A false invariant property: (bits != 2**bit_count-1)
    false_prop = bits.NotEquals(2**bit_count -1)

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
