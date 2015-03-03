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
import cStringIO
from collections import namedtuple

import pysmt.smtlib.commands as smtcmd
from pysmt.exceptions import UnknownSmtLibCommandError
from pysmt.shortcuts import And
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.logics import UFLIRA

class Annotations(object):

    def __init__(self, initial_annotations=None):
        if initial_annotations is not None:
            self._annotations = initial_annotations
        else:
            self._annotations = {}
        self._reversed = {}


    def add(self, formula, annotation, value=None):
        """Adds an annotation for the given formula, possibly with the
        specified value"""
        term_annotations = self._annotations.setdefault(formula, {})
        values = term_annotations.setdefault(annotation, set())
        if value is not None:
            values.add(value)


    def remove(self, formula, annotation, value=None):
        """Adds an annotation for the given formula, possibly with the
        specified value"""
        term_annotations = self._annotations.setdefault(formula, {})
        term_annotations[annotation] = value


    def annotations(self, formula):
        """Returns a dictionary containing all the annotations for the given
        formula as keys and the respective values. None is returned if
        formula has no annotations.
        """
        try:
            return self._annotations[formula]
        except KeyError:
            return None


    def all_annotated_formulae(self, annotation, value=None):
        """Returns the set of all the formulae having the given annotation
        key. If Value is specified, only the formula having the
        specified value are returned.
        """
        res = []
        for f,amap in self._annotations.iteritems():
            if annotation in amap:
                if value is None:
                    res.append(f)
                else:
                    if value in amap[annotation]:
                        res.append(f)
        return res
