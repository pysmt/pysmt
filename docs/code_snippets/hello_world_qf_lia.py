from pysmt.shortcuts import Symbol, LE, GE, Int, And, Equals, Plus, Solver
from pysmt.typing import INT

hello = [Symbol(s, INT) for s in "hello"]
world = [Symbol(s, INT) for s in "world"]

letters = set(hello+world)

domains = And(And(LE(Int(1), l),
                  GE(Int(10), l)) for l in letters)

sum_hello = Plus(hello)
sum_world = Plus(world)

problem = And(Equals(sum_hello, sum_world),
              Equals(sum_hello, Int(25)))

formula = And(domains, problem)

print("Serialization of the formula:")
print(formula)

with Solver(logic="QF_LIA") as solver:
    solver.add_assertion(domains)
    if not solver.solve():
        print("Domain is not SAT!!!")
        exit()
    solver.add_assertion(problem)
    if solver.solve():
        for l in letters:
            print("%s = %s" %(l, solver.get_value(l)))
    else:
        print("No solution found")
