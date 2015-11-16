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
