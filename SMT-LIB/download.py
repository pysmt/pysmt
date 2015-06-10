#!/usr/bin/python
# Downloads and Extracts the specified SMTLIB benchmark

import urllib
import zipfile
import os.path

class BenchmarkNotFoundError(Exception):
    pass

def load_data(filename):
    with open(filename, "r") as fin:
        raw_data = fin.readlines()
        return (line.split() for line in raw_data)

def get_available_benchmarks(data):
    return (d[0] for d in data)

def download_benchmark(benchmark, target_file, force_download=False):
    for (name, url) in load_data("smtlib.urls"):
        if name == benchmark:
            if force_download or not os.path.exists(name):
                urllib.urlretrieve(url, target_file)
            return
    raise BenchmarkNotFoundError()

def download_benchmarks(benchmarks, verbose=True):
    for (name, target) in benchmarks:
        if verbose: print("Downloading %s..." % name)
        download_benchmark(name, target)
        if verbose: print("Completed.")

def unzip_benchmarks(benchmarks, verbose=True):
    for (name, target) in benchmarks:
        if verbose: print("Extracting %s..." % name)
        with zipfile.ZipFile(target, "r") as z:
            z.extractall()

    if verbose: print("Completed.")


if __name__ == "__main__":
    benchmarks = [ ("LIA", "LIA.zip"),
                   ("LRA", "LRA.zip"),
                   ("QF_IDL", "QF_IDL.zip"),
                   ("QF_LIA", "QF_LIA.zip"),
                   ("QF_LRA", "QF_LRA.zip"),
                   ("QF_RDL", "QF_RDL.zip"),

                ]

    download_benchmarks(benchmarks)
    unzip_benchmarks(benchmarks)
