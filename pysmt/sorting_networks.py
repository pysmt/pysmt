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
"""
This module defines SortingNetwork class and functions
"""

import pysmt.environment
from six.moves import range 

class SortingNetwork(object):
    """Provides an efficient encoding for counting elements. """

    [MOD_OE, MOD_EE, MOD_EO, MOD_OO] = range(4)

    def __init__(self, mgr=None):
        if mgr is not None:
            self.mgr = mgr
            self.env = self.mgr.env
        else:
            self.env = pysmt.environment.get_env()
            self.mgr = self.env.formula_manager
        self.And = self.mgr.And
        self.Or = self.mgr.Or
        self._cache = {}

    def at_most_k(self, k, formulae):
        assert(k > 0)
        if(k >= len(formulae)):
            return self.mgr.TRUE()

        sn = self.sorting_network(formulae)

        return self.mgr.Not(sn[k])

    def at_least_k(self, k, formulae):
        assert(k > 0)
        if(k > len(formulae)):
            return self.mgr.FALSE()

        sn = self.sorting_network(formulae)
        return sn[k-1]

    def exactly_k(self, k, formulae):
        assert(k > 0)
        if(k > len(formulae)):
            return self.mgr.FALSE()

        sn = self.sorting_network(formulae)

        if(k == len(formulae)):
            return sn[k-1]
        else:
            return self.mgr.And(sn[k-1],
                                self.mgr.Not(sn[k]))

    def sorting_network(self, formulae):
        """ Returns a list of sorting networks over formulae

        Given formulae = phi1, phi2, ..., phiN, and defining the operator
        true_evals(formulae) that returns the number of functions that evaluates to true.
        The result of sorting_network(formulae) = gamma1, gamma2, ..., gammaN where
        gamma1 <-> (true_evals(formulae) >= 1),
        gamma2 <-> (true_evals(formulae) >= 2),
        ...
        gammaN <-> (true_evals(formulae) >= N),
        """
        key = tuple(formulae)

        output = self._sorting_network(list(formulae))

        if key in self._cache:
            return self._cache[key]
        else:
            output = self._sorting_network(list(formulae))
            self._cache[key] = output
            return output

    def _sorting_network(self, inputs):
        """Given a list of formualae it generates its sorting network circuitry. """

        
        # This function is the iterave version of a standard bisection recursion: 
        # return _sorting_network(inputs[:pivot], inputs[pivot:])

        if(len(inputs) == 1):
            return inputs

        if(len(inputs) == 2):
            return self.two_comparator(inputs[0], inputs[1])

        # list of elements to be processed
        to_process = [inputs]
        # list of positions where "merge" function must be called
        positions = []

        # Main loop collecting the sub elements to be processed 
        pos = 0
        while True:
            el = to_process[pos]

            # Splitting of the element into two parts
            pivot = len(el) // 2
            el1 = el[:pivot]
            el2 = el[pivot:]

            # Substituting the element with the two sub-calls
            to_process[pos] = el2
            to_process.insert(pos, el1)
            
            # Adding the position to the list
            positions.append(pos)

            # Skipping already processed elements
            while (pos < len(to_process)) and (len(to_process[pos]) < 2):
                pos += 1

            # Break condition, when the position pos exceeded the last
            # element 
            
            if pos > len(to_process)-1:
                break

        # Reversing the call list
        positions.reverse()

        # Applying the merge function to each sub element
        for pos in positions:
            to_process[pos] = self.merge(to_process[pos], to_process[pos+1])

            del(to_process[pos+1])

        return to_process[0]


    def two_comparator(self, input1, input2):
        return [self.Or(input1, input2),
                self.And(input1, input2)]

    def combine_results(self, input_odd, input_even, mode):

        if(len(input_odd) == 0):
            return input_even
        if(len(input_even) == 0):
            return input_odd
        if((len(input_odd) == 1) and (len(input_even) == 1)):
            return self.two_comparator(input_odd[0], input_even[0])        
        output_odd = input_odd
        output_even = input_even

        output = []

        assert(mode != self.MOD_OE)

        if (mode == self.MOD_EE):

            first_output_odd = output_odd[0]
            last_output_even = output_even[-1]

            output.append(first_output_odd)

            for i in range(len(output_odd)-1):
                el_odd = output_odd[i+1]
                el_even = output_even[i]
                tp = self.two_comparator(el_odd, el_even)
                output.append(tp[0])
                output.append(tp[1])
            output.append(last_output_even)

        if (mode == self.MOD_EO):

            first_output_odd = output_odd[0]
            output.append(first_output_odd)

            for i in range(len(output_even)):
                el_odd = output_odd[i+1]
                el_even = output_even[i]
                tp = self.two_comparator(el_odd, el_even)
                output.append(tp[0])
                output.append(tp[1])

        if (mode == self.MOD_OO):

            first_output_odd = output_odd[0]
            last_output_odd = output_odd[-1]

            output.append(first_output_odd)

            for i in range(len(output_even)):
                el_odd = output_odd[i+1]
                el_even = output_even[i]
                tp = self.two_comparator(el_odd, el_even)
                output.append(tp[0])
                output.append(tp[1])

            output.append(last_output_odd)


        return output


    def _comp_mode(self, linput1, linput2):
        """ Merging mode computation. """

        is_input1_even = ((linput1 % 2) == 0)
        is_input2_even = ((linput2 % 2) == 0)
        is_input1_odd = not is_input1_even
        is_input2_odd = not is_input2_even

        mode = self.MOD_OE if (is_input1_odd and is_input2_even) else \
               self.MOD_EE if (is_input1_even and is_input2_even) else \
               self.MOD_EO if (is_input1_even and is_input2_odd) else \
               self.MOD_OO if (is_input1_odd and is_input2_odd) else -1

        return mode

    def merge(self, input1, input2):
        """Given two list of formualae it merges them. """

        if (len(input1) == 0):
            return input2

        if (len(input2) == 0):
            return input1

        if (len(input1) == 1) and (len(input2) == 1):
            return self.two_comparator(input1[0], input2[0])

        # Computing the subsets of input calls
        (to_process, positions) = self._merge_calls(input1, input2)
        # Executing the calls for each positions
        outputs = self._merge_exec(to_process, positions)

        return outputs



    def _merge_calls(self, input1, input2):
        """Given two list of formualae it computes the set of calls
        for merge function. """

        # List of the calls to the "combine_results" function
        to_process = [[input1, input2]]
        # List of call positions
        positions = []

        # Main loop collecting the sub elements to be processed
        pos = 0
        while True:
            el1 = to_process[pos][0]
            el2 = to_process[pos][1]

            mode = self._comp_mode(len(el1), len(el2))

            if mode == self.MOD_OE:
                mode = self.MOD_EO
                (el1, el2) = (el2, el1)

            if (len(el1) > 0) and (len(el2) > 0):
                # Call splitting (odd, odd and even, even elements)
                call1 = [el1[0:][::2]] + [el2[0:][::2]]
                call2 = [el1[1:][::2]] + [el2[1:][::2]]

                # Substituting the elements with the two sub-calls
                to_process[pos] = call2
                to_process.insert(pos, call1)

                # Adding the position to the list
                positions.append((pos, mode))
            else:
                # No other calls to be processed
                break

            # Skipping already processed elements
            while True:
                cur_el = to_process[pos]

                if (# it is not at the end of the list
                    (pos < len(to_process)-1) and 
                    # AND one of the calls is empty
                    (((len(cur_el[0]) < 1) or  (len(cur_el[1]) < 1)) or 
                    # OR both calls contain just one element
                     ((len(cur_el[0]) < 2) and (len(cur_el[1]) < 2)))):
                    pos += 1
                else:
                    break


        # Computing the top level mode
        mode = self._comp_mode(len(input1), len(input2))

        if mode == self.MOD_OE:
            mode = self.MOD_EO
            (input1, input2) = (input2, input1)

        # Reversing the call list
        positions.reverse()

        # Adding the top level merge call
        positions.append((0, mode))

        return (to_process, positions)


    def _merge_exec(self, to_process, positions):
        """Given the set of calls, and positions it executes
        the "combine_results" on them. """

        # Applying the "combine_results" function to each sub element
        i = 0
        for op in positions:
            i += 1
            (pos, mode) = op

            if i != len(positions): 
                mode1 = (0 if (len(to_process[pos]) == 2) else to_process[pos][2])
                mode2 = (0 if (len(to_process[pos+1]) == 2) else to_process[pos+1][2])

                out1 = self.combine_results(to_process[pos][0], to_process[pos][1], mode1)
                out2 = self.combine_results(to_process[pos+1][0], to_process[pos+1][1], mode2)

                to_process[pos] = [out1, out2, mode]
                del(to_process[pos+1])
            else:
                to_process = self.combine_results(to_process[pos][0], to_process[pos][1], mode)

        return to_process
