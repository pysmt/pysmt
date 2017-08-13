import os
import time
import sys
import random
import multiprocessing
import argparse

from itertools import islice

from pysmt.shortcuts import reset_env, read_smtlib


def get_all_smt_files(target_dir=None):
    if target_dir == None:
        target_dir = "./"

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
    start = time.clock()
    read_smtlib(smtfile)
    end = time.clock()
    return ( (end - start), smtfile)


def dump_stats(timings, fname):
    if fname is None:
        fname = "stats.out"
    with open(fname, "w") as f:
        f.write('filename, time\n')
        for k in timings:
            f.write('%f, "%s"\n' % k)


def main():
    parser = argparse.ArgumentParser(description='SMT-LIB Parser Benchmarking')
    parser.add_argument('--base', type=str, nargs='?',
                        help='top-directory of the benchmarks')

    parser.add_argument('--count', type=int, nargs='?',
                        default=-1,
                        help='number of files to benchmark')

    parser.add_argument('--out', type=str, default="stats.out", nargs='?',
                        help='Where to save the statistics')

    args = parser.parse_args()

    random.seed(42)
    p = multiprocessing.Pool()
    chunks = multiprocessing.cpu_count()
    file_list = list(get_all_smt_files(args.base))
    random.shuffle(file_list)
    if args.count == -1:
        files_cnt = len(file_list)
    else:
        files_cnt = args.count
    print("Submitting %d jobs, %d at the time" % (files_cnt, chunks))
    timings = p.map(execute_script_fname, islice(file_list, files_cnt), chunks)

    mean = sum(x[0] for x in timings) / len(timings)
    print("The mean execution time was %0.2f seconds" % mean)
    print("The max execution time was %0.2f seconds" % max(x[0] for x in timings))

    outfile = args.out
    dump_stats(timings, outfile)
    print("The statistics file has been generated in '%s'" % outfile)


if __name__ == '__main__':
    main()
