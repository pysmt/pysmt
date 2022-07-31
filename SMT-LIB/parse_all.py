import os
from timeit import timeit
import random
import multiprocessing
import argparse

from itertools import islice, repeat

from pysmt.shortcuts import reset_env, read_smtlib


def get_all_smt_files(target_dir=None):
    if target_dir is None:
        target_dir = "./"

    assert os.path.exists(target_dir)
    for root, _, files in os.walk(target_dir):
        for f in files:
            if f.endswith(".smt2") or f.endswith(".smt2.bz2"):
                yield os.path.join(root, f)


def execute_script_fname(smtfile, reps):
    """Read and call a Solver to solve the instance"""
    print(smtfile)
    reset_env()
    assert os.path.exists(smtfile)
    assert reps > 0
    try:
        exec_time = timeit(lambda: read_smtlib(smtfile, False), number=reps)
    except:
        exec_time = -1
    return (exec_time, smtfile)


def dump_stats(timings, fname):
    if fname is None:
        fname = "stats.out"
    with open(fname, mode='w', encoding="utf-8") as f:
        f.write('filename, time\n')
        for val, bench_name in timings:
            f.write(f'"{bench_name}", {val}\n')


def main():
    parser = argparse.ArgumentParser(description='SMT-LIB Parser Benchmarking')
    parser.add_argument('--base', type=str, nargs='?',
                        help='top-directory of the benchmarks')

    parser.add_argument('--count', type=int, nargs='?',
                        default=-1,
                        help='number of files to benchmark')

    parser.add_argument('--out', type=str, default="stats.out", nargs='?',
                        help='Where to save the statistics')

    parser.add_argument('--reps', type=int, default=1,
                        help="number of times each benchmark is run")

    args = parser.parse_args()

    random.seed(42)
    chunks = multiprocessing.cpu_count()
    file_list = list(get_all_smt_files(args.base))
    random.shuffle(file_list)
    if args.count == -1:
        files_cnt = len(file_list)
    else:
        files_cnt = args.count

    timings = []
    errors = []

    with multiprocessing.Pool() as p:
        print(f"Submitting {files_cnt} jobs, {chunks} at the time")
        for el in p.starmap(execute_script_fname,
                            zip(islice(file_list, files_cnt),
                                repeat(args.reps)),
                            chunks):
            (timings if el[0] > 0 else errors).append(el)

    mean = sum(x[0] for x in timings) / len(timings)
    print(f"The mean execution time was {mean:.2f} seconds")
    print(f"The max execution time was {max(x[0] for x in timings):.2f} seconds")
    print(f"Found {len(errors)} errors: {[x[1] for x in errors]}")

    outfile = args.out
    dump_stats(timings, outfile)
    print(f"The statistics file has been generated in '{outfile}'")


if __name__ == '__main__':
    main()
