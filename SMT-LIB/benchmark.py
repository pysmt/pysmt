import os
import time
import sys
import random
import multiprocessing
import argparse

from itertools import islice

from pysmt.shortcuts import reset_env, read_smtlib

# Map function name to function instance
ALL_FUNC = {}
def register(func):
    ALL_FUNC[func.__name__] = func

def benchmark_func(args):
    """Run the benchmark function.

    Takes care of the boilerplate of logging and timing
    """
    b, smtfile = args
    func = ALL_FUNC[b]
    print(smtfile)
    reset_env()
    assert os.path.exists(smtfile)
    start = time.clock()
    func(smtfile)
    end = time.clock()
    return ((end - start), smtfile)

def get_all_smt_files(target_dir=None):
    if target_dir == None:
        target_dir = "./"
    assert os.path.exists(target_dir)
    return (os.path.join(root, f)
            for root, _, files in os.walk(target_dir)
            for f in files if f.endswith(".smt2"))

@register
def parse(smtfile):
    """Parse the SMT-LIB file"""
    read_smtlib(smtfile)
    return None

@register
def hr_print(smtfile):
    """Read and print the formula in HR Format."""
    f = read_smtlib(smtfile)
    f.serialize()
    return None

@register
def simplify(smtfile):
    """Simplify a file."""
    f = read_smtlib(smtfile)
    f.simplify()

@register
def simplify_validate(smtfile):
    """Validate a simplification."""
    from pysmt.shortcuts import is_valid, Iff
    f = read_smtlib(smtfile)
    g = f.simplify()
    assert is_valid(Iff(f,g))

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
                        default=0,
                        help='number of files to benchmark')

    parser.add_argument('--out', type=str, default="stats.out", nargs='?',
                        help='Where to save the statistics')

    parser.add_argument('--bench', type=str, help="Which benchmark to run", default="parse")

    parser.add_argument('--file-list', type=str, help="Consider only the files in the file list")

    args = parser.parse_args()
    benchmark = args.bench

    # Prepare files
    if args.file_list:
        with open(args.file_list, "r") as fin:
            file_list = [f.split(",")[1].replace('"','').strip() for f in fin.readlines()[1:]]
    else:
        print("Computing file list")
        file_list = list(get_all_smt_files(args.base))
        random.shuffle(file_list)
    files_cnt = len(file_list)
    if args.count:
        if args.count > files_cnt:
            print("Not enough files (requested %d, available %d)" % (args.count, files_cnt))
            exit(-1)
        files_cnt = args.count

    # Setup threads
    random.seed(42)
    p = multiprocessing.Pool()
    chunks = multiprocessing.cpu_count()
    print("Submitting %d jobs, %d at the time" % (files_cnt, chunks))
    files = ((benchmark, f) for f in islice(file_list, files_cnt))
    timings = p.map(benchmark_func, files, chunks)

    # Compute stats
    total = sum(x[0] for x in timings)
    mean = total / len(timings)
    print("The total execution time was %0.2f seconds" % total)
    print("The mean execution time was %0.2f seconds" % mean)
    print("The max execution time was %0.2f seconds" % max(x[0] for x in timings))

    outfile = args.out
    dump_stats(timings, outfile)
    print("The statistics file has been generated in '%s'" % outfile)


if __name__ == '__main__':
    main()
