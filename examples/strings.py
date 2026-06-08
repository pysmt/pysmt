# The example requires cvc5 or Z3 to be installed
#
# The theory of strings defines a way to operate on sequences of ASCII
# characters.
#
# The example mimics a password validator, validates a password given
# as input and returns a new more "secure" password if the validation
# fails.
#
from pysmt.shortcuts import (String, StrLength, StrContains, StrConcat,
                             StrReplace,
                             IntToStr, Ite, Symbol, And, Or, Not, Int,
                             get_model)
from pysmt.typing import STRING, INT

password_in = Symbol("password_in", STRING)
password_out = Symbol("password_out", STRING)

# Define a predicate that encodes some general rules
def is_good_password(password):
    return And(
        # 1. Length >=8 char
        StrLength(password) >= 8,
        # 2. Contains a digit
        Or(StrContains(password, IntToStr(Int(x))) for x in range(10)),
        # 3. Does not contain the word 'password'
        Not(StrContains(password, String("password"))))

# Transform the input password to make it stronger .
# We return a tuple. The first element is the new password, and the
# second are additional constraints
def strengthen_password(password):
    s = password
    pad = Symbol("padding", STRING)
    randint = Symbol("d", INT)
    # Change word 'password' if it occurs with 'pySMT'
    s = StrReplace(s, String("password"), String("pySMT"))
    # Add some random digits
    s = StrConcat(s, IntToStr(randint))
    # Add padding
    s = StrConcat(s, pad)
    # Ensure total length is > = 10
    f = And(StrLength(s) >= 10,
            # And that randint is a natural number
            # Otherwise IntToStr returns the empty string
            randint >= 0)
    return s, f

# Create a strong passowrd from the initial one
new_password, constr = strengthen_password(password_in)

# If the input password is strong, if not, use the strengthen_password
check = And(password_out.Equals(Ite(is_good_password(password_in),
                                    password_in,
                                    new_password)),
            constr)

# Run the example by providing an example password to be checked
import sys
if len(sys.argv) >= 2:
    user_pass = sys.argv[1]
else:
    print("Usage %s <password>" % sys.argv[0])
    user_pass = "ABc"

m1 = get_model(And(password_in.Equals(String(user_pass)),
                  check))
print(m1[password_out])

# Is our 'strengthen' procedure always yielding a strong password?
# Can you think of an input that would not be properly sanitized?
m2 = get_model(And(check,
                   Not(is_good_password(password_out))))
print(m2[password_in])
