# This example shows a more advance use of pySMT.
#
# It provides a simple implementation of Bounded Model Checking [1]
# and K-Induction [2] and applies it on a simple infinite-state
# transition system.
#
# [1] ...
#
# [2] ...
#
from six.moves import xrange

from pysmt.shortcuts import Symbol, Not, Equals, And, Times, Int, Plus, LE, Or, EqualsOrIff
from pysmt.shortcuts import is_sat, is_unsat
from pysmt.typing import INT


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



def get_subs(system, i):
    """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
    subs_i = {}
    for v in system.variables:
        subs_i[v] = at_time(v, i)
        subs_i[next_var(v)] = at_time(v, i+1)
    return subs_i


def get_unrolling(system, k):
    """Unrolling of the transition relation from 0 to k:

    E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
    """
    res = []
    for i in xrange(k+1):
        subs_i = get_subs(system, i)
        res.append(system.trans.substitute(subs_i))
    return And(res)


def get_simple_path(system, k):
    """Simple path constraint for k-induction:
    each time encodes a different state
    """
    res = []
    for i in xrange(k+1):
        subs_i = get_subs(system, i)
        for j in xrange(i+1, k+1):
            state = []
            subs_j = get_subs(system, j)
            for v in system.variables:
                v_i = v.substitute(subs_i)
                v_j = v.substitute(subs_j)
                state.append(Not(EqualsOrIff(v_i, v_j)))
            res.append(Or(state))
    return And(res)


def get_k_hypothesis(system, prop, k):
    """Hypothesis for k-induction: each state up to k-1 fulfills the property"""
    res = []
    for i in xrange(k):
        subs_i = get_subs(system, i)
        res.append(prop.substitute(subs_i))
    return And(res)


def get_bmc(system, prop, k):
    """Returns the BMC encoding at step k"""
    init_0 = system.init.substitute(get_subs(system, 0))
    prop_k = prop.substitute(get_subs(system, k))
    return And(get_unrolling(system, k), init_0, Not(prop_k))

def get_k_induction(system, prop, k):
    """Returns the K-Induction encoding at step K"""
    subs_k = get_subs(system, k)
    prop_k = prop.substitute(subs_k)
    return And(get_unrolling(system, k),
               get_k_hypothesis(system, prop, k),
               get_simple_path(system, k),
               Not(prop_k))

def check_property(system, prop):
    """Interleaves BMC and K-Ind to verify the property."""
    print("Checking property %s..." % prop)
    for b in xrange(100):
        f = get_bmc(system, prop, b)
        print("   [BMC]    Checking bound %d..." % (b+1))
        if is_sat(f):
            print("--> Bug found at step %d" % (b+1))
            return

        f = get_k_induction(system, prop, b)
        print("   [K-IND]  Checking bound %d..." % (b+1))
        if is_unsat(f):
            print("--> The system is safe!")
            return


def main():
    # Example Transition System (SMV-like syntax)
    #
    # VAR x: integer;
    #     y: integer;
    #
    # INIT: x = 1 & y = 2;
    #
    # TRANS: next(x) = x + 1;
    # TRANS: next(y) = y + 2;

    x, y = [Symbol(s, INT) for s in "xy"]
    nx, ny = [next_var(Symbol(s, INT)) for s in "xy"]

    example = TransitionSystem(variables = [x, y],
               init = And(Equals(x, Int(1)),
                          Equals(y, Int(2))),
               trans = And(Equals(nx, Plus(x, Int(1))),
                           Equals(ny, Plus(y, Int(2)))))

    # A true invariant property: y = x * 2
    true_prop = Equals(y, Times(x, Int(2)))

    # A false invariant property: x <= 10
    false_prop = LE(x, Int(10))

    for prop in [true_prop, false_prop]:
        check_property(example, prop)
        print("")

if __name__ == "__main__":
    main()
