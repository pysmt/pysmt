#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
import os

from pysmt.exceptions import PysmtImportError
#
# Try to import the Cython version of the parser.
# Fall-back on the pure-python version if:
#  - Cython is not installed
#  - There is an error in the handling of the pyx file and the use of
#    Cython was not specified (unset env variable)
#
ENV_USE_CYTHON = os.environ.get("PYSMT_CYTHON")
if ENV_USE_CYTHON is not None:
    ENV_USE_CYTHON = ENV_USE_CYTHON.lower() in ["true", "1"]

HAS_CYTHON = False
try:
    import pyximport
    HAS_CYTHON = True
except ImportError as ex:
    if ENV_USE_CYTHON:
        raise PysmtImportError(str(ex))

if HAS_CYTHON and (ENV_USE_CYTHON or ENV_USE_CYTHON is None):
    USE_CYTHON = True
else:
    USE_CYTHON = False

if USE_CYTHON:
    try:
        pyximport.install()
        from pysmt.smtlib.parser.parser import *
    except ImportError as ex:
        if ENV_USE_CYTHON is None:
            # If not specified, fall-ack
            USE_CYTHON = False
        else:
            raise PysmtImportError(str(ex))

if not USE_CYTHON:
    from pysmt.smtlib.parser.parser import *
else:
    # pyximport.install() would be sufficient if we had a .pyx file
    # However, we currently are not annotating the .py file for cython,
    # and therefore our .pyx file would be a copy of the .py file.
    #
    # To avoid code duplication, we tell cython to compile the .py file
    # and load the resulting .so file. Cython does not support this flow,
    # therefore we need to have a couple of work-arounds.
    #
    # 1. Call to pyximport.install(): Functions in pyximport expect to
    # find a global object called pyxargs. This is created within
    # install(). We could call uninstall() afterwards, to avoid
    # enabling cython globally.
    #
    # 2. build_dir: Also this variable is set in install(). We use the
    # default value, that is a folder in the home-dir.
    #
    # 3. load_dynamic will load the module but not extend the globald
    # directory. We rely on the fact that the loading has been already
    # performed and call the import * explicitly
    #
    # Since the .so is compiled outside of the PYTHON_PATH, there is
    # no ambiguity when importing the parser: the only way to load the
    # cython version is by the so_path that targets .pyxbld .
    #
    import imp

    pyx = pyximport.install()
    pyximport.uninstall(*pyx)
    build_dir = os.path.join(os.path.expanduser('~'), '.pyxbld')
    path = os.path.join(os.path.dirname(__file__), "parser.py")
    name="pysmt.smtlib.parser.parser"

    so_path = pyximport.build_module(name, path,
                                     pyxbuild_dir=build_dir)
    mod = imp.load_dynamic(name, so_path)
    assert mod.__file__ == so_path, (mod.__file__, so_path)
    # print(so_path)
    from pysmt.smtlib.parser.parser import *


# End of preamble

#
#
#
if __name__ == "__main__":
    import sys

    def main():
        """Simple testing script"""
        args = sys.argv
        out = None
        if len(args) == 3:
            out = args[2]
        elif len(args) != 2:
            print("Usage %s <file.smt2> [out.smt2]" % args[0])
            exit(1)

        fname = args[1]

        parser = SmtLibParser()
        res = parser.get_script_fname(fname)
        assert res is not None
        print("Done")
        if out is not None:
            res.to_file(out, daggify=True)
    main()
