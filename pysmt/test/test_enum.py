if __name__ == "__main__":
    colors = EnumType("white", "red", "yellow", "green")
    x = colors.Symbol("x")
    y = colors.Symbol("y")
    red = colors.Const("red")
    yellow = colors.Const("yellow")
    print(colors)
    print(x)
    print(red)
    print("Encode red: %s" % red.encode(x))
    print("Encode yellow: %s" % yellow.encode(x))
    print("Encode green: %s" % colors.Const("green").encode(x))
    print(" x = red  ===> %s" % EnumEquals(x, red))
    print(" x = x  ===> %s" % EnumEquals(x, x))
    print("Domain Constrain: %s" % x.encode_domain())

    assert red == colors.Const("red")
    assert x == colors.Symbol("x")
    assert x != colors.Symbol("y")

    try:
        colors.Const("invalid")
        assert False
    except InvalidEnumValue:
        pass


    problem = And(Not(EnumEquals(x,y)),
                  EnumEquals(x, red),
                  Not(EnumEquals(y, colors.Const("white"))),
                  Not(EnumEquals(y, colors.Const("yellow"))))
    print(problem)
    problem = And(problem,
                  x.encode_domain(),
                  y.encode_domain())

    with Solver() as s:
        s.add_assertion(problem)
        assert s.solve()
        m = s.get_model()
        value_x = colors.decode_value(x, m)
        value_y = colors.decode_value(y, m)
        print("x: %s" % value_x)
        print("y: %s" % value_y)
        assert value_x == red
        assert value_y == colors.Const("green")
