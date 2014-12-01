from pysmt.shortcuts import Symbol, And, Not, FALSE, Solver

with Solver() as solver:

    varA = Symbol("A") # Default type is Boolean
    varB = Symbol("B")

    f = And([varA, Not(varB)])

    print(f)

    g = f.substitute({varB:varA})

    print(g)

    solver.add_assertion(g)
    res = solver.solve()
    assert not res

    h = And(g, FALSE())
    simp_h = h.simplify()
    print(h, "-->", simp_h)

    print("OK")
