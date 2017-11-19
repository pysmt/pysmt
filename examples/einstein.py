#
# This example requires MathSAT or Z3
#
# In this example, we will encode a more complex puzzle and see:
#
# - Use of UNSAT cores as a debugging tool
# - Conjunctive partitioning
# - Symbol handling delegation to auxiliary functions
#

# This puzzle is known as Einstein Puzzle
#
# There are five houses in five different colours in a row. In each
# house lives a person with a different nationality. The five owners
# drink a certain type of beverage, smoke a certain brand of cigar and
# keep a certain pet.
#
# No owners have the same pet, smoke the same brand of cigar, or drink
# the same beverage.
#
# The Brit lives in the red house.
# The Swede keeps dogs as pets.
# The Dane drinks tea.
# The green house is on the immediate left of the white house.
# The green house owner drinks coffee.
# The owner who smokes Pall Mall rears birds.
# The owner of the yellow house smokes Dunhill.
# The owner living in the center house drinks milk.
# The Norwegian lives in the first house.
# The owner who smokes Blends lives next to the one who keeps cats.
# The owner who keeps the horse lives next to the one who smokes Dunhill.
# The owner who smokes Bluemasters drinks beer.
# The German smokes Prince.
# The Norwegian lives next to the blue house.
# The owner who smokes Blends lives next to the one who drinks water.
#
# The question is: who owns the fish?

from pysmt.shortcuts import (Symbol, ExactlyOne, Or, And, FALSE, TRUE,
                             Iff, Implies)
from pysmt.shortcuts import get_model, get_unsat_core, is_sat, is_unsat

#
# Lets start by expliciting all values for all dimensions

Color = "white", "yellow", "blue", "red", "green"
Nat = "german", "swedish", "british", "norwegian", "danish"
Pet =  "birds", "cats", "horses", "fish", "dogs"
Drink = "beer", "water", "tea", "milk", "coffee"
Smoke = "blends", "pall_mall", "prince", "bluemasters", "dunhill"
Houses = range(0,5)
#
# We number the houses from 0 to 4, and create the macros to assert
# properties of the i-th house:
#
#  e.g., color(1, "green")  to indicate that the house 1 is Green
#
# This is not strictly necessary, but it is a way of making programs
# more readable.
#
def color(number, name):
    assert name in Color
    if number in Houses:
        return Symbol("%d_color_%s" % (number, name))
    return FALSE()

def nat(number, name):
    assert name in Nat
    if number in Houses:
        return Symbol("%d_nat_%s" % (number, name))
    return FALSE()

def pet(number, name):
    assert name in Pet
    if number in Houses:
        return Symbol("%d_pet_%s" % (number, name))
    return FALSE()

def drink(number, name):
    assert name in Drink
    if number in Houses:
        return Symbol("%d_drink_%s" % (number, name))
    return FALSE()

def smoke(number, name):
    assert name in Smoke
    if number in Houses:
        return Symbol("%d_smoke_%s" % (number, name))
    return FALSE()

#
# We can encode the facts
#

facts = TRUE()
for i in Houses:
    facts = (facts &
        # The Brit lives in the red house.
        nat(i, "british").Iff(color(i, "red")) &

        # The Swede keeps dogs as pets.
        nat(i, "swedish").Iff(pet(i, "dogs")) &

        # The Dane drinks tea.
        nat(i, "danish").Iff(drink(i, "tea")) &

        # The green house is on the immediate left of the white house.
        color(i, "green").Iff(color(i+1, "white")) &

        # The green house owner drinks coffee.
        color(i, "green").Iff(drink(i, "coffee")) &

        # The owner who smokes Pall Mall rears birds.
        smoke(i, "pall_mall").Iff(pet(i, "birds")) &

        # The owner of the yellow house smokes Dunhill.
        color(i, "yellow").Iff(smoke(i, "dunhill")) &

        # The owner who smokes Bluemasters drinks beer.
        smoke(i, "bluemasters").Iff(drink(i, "beer")) &

        # The German smokes Prince.
        nat(i, "german").Iff(smoke(i, "prince")) &

        # The owner who smokes Blends lives next to the one who keeps cats.
        smoke(i, "blends").Implies(pet(i-1, "cats") | pet(i+1, "cats")) &

        # The owner who keeps the horse lives next to the one who smokes Dunhill.
        pet(i, "horses").Implies(smoke(i-1, "dunhill") | smoke(i+1, "dunhill")) &

        # The Norwegian lives next to the blue house.
        # Carefull with this one!
        nat(i, "norwegian").Iff(color(i-1, "blue") | color(i+1, "blue")) &

        # The owner who smokes Blends lives next to the one who drinks water.
        smoke(i, "blends").Implies(drink(i-1, "water") | drink(i+1, "water"))
    )

facts = And(facts,
            # The owner living in the center house drinks milk.
            drink(2, "milk"),

            # The Norwegian lives in the first house.
            nat(0, "norwegian")
)


domain = And(
    And(ExactlyOne(color(i, c) for i in Houses) for c in Color),
    And(ExactlyOne(nat(i, c) for i in Houses) for c in Nat),
    And(ExactlyOne(pet(i, c) for i in Houses) for c in Pet),
    And(ExactlyOne(drink(i, c) for i in Houses) for c in Drink),
    And(ExactlyOne(smoke(i, c) for i in Houses) for c in Smoke),
    #
    And(ExactlyOne(color(i, c) for c in Color) for i in Houses),
    And(ExactlyOne(nat(i, c) for c in Nat) for i in Houses),
    And(ExactlyOne(pet(i, c) for c in Pet) for i in Houses),
    And(ExactlyOne(drink(i, c) for c in Drink) for i in Houses),
    And(ExactlyOne(smoke(i, c) for c in Smoke) for i in Houses),
    )

problem = domain.And(facts)

model = get_model(problem)

if model is None:
    print("UNSAT")
    # We first check whether the constraints on the domain and problem
    # are satisfiable in isolation.
    assert is_sat(facts)
    assert is_sat(domain)
    assert is_unsat(problem)

    # In isolation they are both fine, rules from both are probably
    # interacting.
    #
    # The problem is given by a nesting of And().
    # conjunctive_partition can be used to obtain a "flat"
    # structure, i.e., a list of conjuncts.
    #
    from pysmt.rewritings import conjunctive_partition
    conj = conjunctive_partition(problem)
    ucore = get_unsat_core(conj)
    print("UNSAT-Core size '%d'" % len(ucore))
    for f in ucore:
        print(f.serialize())

    # The exact version of the UNSAT-Core depends on the solver in
    # use.  Nevertheless, this represents a starting point for your
    # debugging.  A possible way to approach the result is to look for
    # clauses of size 1 (i.e., unit clauses). In the facts list there
    # is only 1 fact:
    #   0_nat_norwegian
    #
    # The clause ("1_color_blue" <-> "0_nat_norwegian")
    # Implies that "1_color_blue"
    # But (("3_color_blue" | "1_color_blue") <-> "2_nat_norwegian")
    # Requires "2_nat_norwegian"
    # The ExactlyOne constraint forbids that both 0 and 2 are nowegian
    # thus, we have a better idea of where the problem might be.
    #
    # Please go back to the comment '# Careful with this!!!' in the
    # facts list, and change the Iff with an Implies.
    #
    # Done?
    #
    # Good, you should be getting a model, now!
else:
    for h in Houses:
        # Extract the relevants bits to get some pretty-printing
        c = [x for x in Color if model[color(h, x)].is_true()][0]
        n = [x for x in Nat if model[nat(h, x)].is_true()][0]
        p = [x for x in Pet if model[pet(h, x)].is_true()][0]
        d = [x for x in Drink if model[drink(h, x)].is_true()][0]
        s = [x for x in Smoke if model[smoke(h, x)].is_true()][0]
        print(h, c, n, p, d, s)
        if p == "fish":
            sol = "The '%s' owns the fish!" % n
    print(sol)
