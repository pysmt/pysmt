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

class QuantifierEliminator(object):

    def eliminate_quantifiers(self, formula):
        """
        Returns a quantifier-free equivalent formula of the given
        formula

        If explicit_vars is specified, an explicit enumeration of all
        the possible models for such variables is computed and
        quantifier elimination is performed on each disjunct
        separately.
        """
        raise NotImplementedError

    def __enter__(self):
        """ Manage entering a Context (i.e., with statement) """
        return self


    def __exit__(self, exc_type, exc_val, exc_tb):
        """ Manage exiting from Context (i.e., with statement)

        The default behaviour is to explicitely destroy the qelim to free
        the associated resources.
        """
        del self
