import os
import time
import sys
import random

from pysmt.shortcuts import reset_env, get_env, read_smtlib


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
    """Read and print the formula in HR Format."""
    reset_env()
    assert os.path.exists(smtfile)
    smtlib_start = time.clock()
    f = read_smtlib(smtfile)
    smtlib_end = time.clock()
    start = time.clock()
    s = f.serialize()
    end = time.clock()
    assert s is not None
    #print(smtfile, (smtlib_end-smtlib_start), (end-start))
    return (smtfile, (end - start))


def dump_stats(timings, fname):
    with open(fname, "w") as f:
        f.write('filename, time\n')
        for k in timings:
            f.write('"%s", "%s"\n' % k)


def main():
    if len(sys.argv) not in (2,3):
        print("usage: %s <number of files to benchmark> [<statistics file>]" %\
              sys.argv[0])
        exit(1)

    random.seed(42)

    file_list = list(get_all_smt_files())
    #random.shuffle(file_list)
    files_cnt = int(sys.argv[1])
    timings = []
    for fname in file_list[:files_cnt]:
        timings.append(execute_script_fname(fname))

    mean = sum(x[1] for x in timings) / len(timings)
    print("The mean execution time is: %f seconds."  % mean)

    if len(sys.argv) == 3:
        outfile = sys.argv[2]
        dump_stats(timings, outfile)
        print("The statistics file has been generated in '%s'" % outfile)


if __name__ == '__main__':
    main()
