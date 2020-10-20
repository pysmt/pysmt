#!/bin/bash
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

export PYTHONDONTWRITEBYTECODE=True

# Skip slow tests (-m "not slow")
# Exit on error (-x)
# Rule of thumb: if a test takes more than 10 seconds it
#                should be marked as slow using:
#                    @pytest.mark.slow
python3 -m pytest -m "not slow" -x pysmt/test
