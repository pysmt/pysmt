from pysmt.rewritings import Ackermanization
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
from pysmt.shortcuts import get_env
from sys import argv
import pprint
pp = pprint.PrettyPrinter(indent=4)


def main(path):
    parser = SmtLibParser()
    script = parser.get_script_fname(path)
    formula = script.get_last_formula()
    a = Ackermanization()
    env = get_env()
    a.do_ackermanization(formula)

if __name__ == '__main__':
    main(argv[1])
