import sys

def is_python_3():
    return sys.version_info >= (3,0)

def is_python_2():
    return not is_python_3()
