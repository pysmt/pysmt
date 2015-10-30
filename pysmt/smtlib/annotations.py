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
from six import iteritems

class Annotations(object):
    """Handles and stores (key,value) annotations for formulae"""

    def __init__(self, initial_annotations=None):
        if initial_annotations is not None:
            self._annotations = initial_annotations
        else:
            self._annotations = {}


    def add(self, formula, annotation, value=None):
        """Adds an annotation for the given formula, possibly with the
        specified value"""
        term_annotations = self._annotations.setdefault(formula, {})
        values = term_annotations.setdefault(annotation, set())
        if value is not None:
            values.add(value)


    def remove(self, formula):
        """Removes all the annotations for the given formula"""
        if formula in self._annotations:
            del self._annotations[formula]


    def remove_annotation(self, formula, annotation):
        """Removes the given annotation for the given formula"""
        if formula in self._annotations:
            if annotation in self._annotations[formula]:
                del self._annotations[formula][annotation]


    def remove_value(self, formula, annotation, value):
        """Removes the given annotation for the given formula"""
        if formula in self._annotations:
            if annotation in self._annotations[formula]:
                d = self._annotations[formula][annotation]
                if value in d:
                    d.remove(value)


    def has_annotation(self, formula, annotation, value=None):
        """Returns True iff the given formula has the given annotation. If
        Value is specified, True is returned only if the value is
        matching.
        """
        if formula in self._annotations:
            if annotation in self._annotations[formula]:
                if value is None:
                    return True
                else:
                    return (value in self._annotations[formula][annotation])
        return False


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
        for f,amap in iteritems(self._annotations):
            if annotation in amap:
                if value is None:
                    res.append(f)
                else:
                    if value in amap[annotation]:
                        res.append(f)
        return set(res)


    def __contains__(self, formula):
        """Checks if formula has at least one annotation"""
        return formula in self._annotations


    def __str__(self):
        res = ["Annotations: {"]
        for t, m in iteritems(self._annotations):
            res.append(str(t) + " -> ")
            for a, lst in iteritems(m):
                res.append(":" + str(a) + "{")
                for v in lst:
                    res.append(str(v) + ", ")
                res.append("} ")
        return "".join(res + ["}"])


    def __getitem__(self, formula):
        return self.annotations(formula)
