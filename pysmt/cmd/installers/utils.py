# Copyright 2014 Andrea Micheli and Marco Gario
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
import sys
import zipfile
import tarfile

from contextlib import contextmanager


def untar(fname, directory, mode='r:gz'):
    """Extracts the tarfile using the specified mode in the given directory."""
    tfile = tarfile.open(fname, mode)
    tfile.extractall(directory)


def unzip(fname, directory):
    """Unzips the given archive into the given directory"""
    myzip = zipfile.ZipFile(fname, "r")
    myzip.extractall(directory)
    myzip.close()


@contextmanager
def TemporaryPath(path):
    """Context that substitutes the system path to test for API presence or absence"""
    old_path = list(sys.path)
    try:
        sys.path = path + sys.path
        yield
    finally:
        sys.path = old_path
