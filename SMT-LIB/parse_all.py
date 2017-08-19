import os
import time
import sys
import random
import multiprocessing

from itertools import islice

from pysmt.shortcuts import reset_env, get_env
from pysmt.smtlib.parser import SmtLibParser
from pysmt.solvers.noop import NoopSolver

SMTLIB_DIR = "./"

def get_all_smt_files(target_dir=None):
    if target_dir == None:
        target_dir = SMTLIB_DIR

    assert os.path.exists(target_dir)
    for root, _, files in os.walk(target_dir):
        for f in files:
            if f.endswith(".smt2"):
                yield os.path.join(root, f)


def execute_script_fname(smtfile):
    """Read and call a Solver to solve the instance"""
    print(smtfile)
    reset_env()
    assert os.path.exists(smtfile)
    parser = SmtLibParser()
    solver = NoopSolver(get_env())

    start = time.clock()
    script = parser.get_script_fname(smtfile)
    end = time.clock()

    script.evaluate(solver)
    res = solver.get_asserted_formula()
    assert res is not None

    return (smtfile, (end - start))


def dump_stats(timings, fname):
    with open(fname, "w") as f:
        f.write('filename, time\n')
        for k in timings:
            f.write('"%s", "%s"\n' % k)


def main():
    if len(sys.argv) != 3:
        print("usage: %s <number of files to benchmark> <statistics file>" %\
              sys.argv[0])
        exit(1)

    random.seed(42)
    p = multiprocessing.Pool()
    chunks = multiprocessing.cpu_count()
    file_list = list(get_all_smt_files())
    random.shuffle(file_list)
    files_cnt = int(sys.argv[1])
    print("Submitting %d jobs, %d at the time" % (files_cnt, chunks))
    timings = p.map(execute_script_fname, islice(file_list, files_cnt), chunks)

    mean = sum(x[1] for x in timings) / len(timings)
    print("The mean execution time is:", mean, "seconds")

    outfile = sys.argv[2]
    dump_stats(timings, outfile)
    print("The statistics file has been generated in '%s'" % outfile)


if __name__ == '__main__':
    main()
