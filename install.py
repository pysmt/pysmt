#!/usr/bin/env python

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

import urllib2
import os
import tarfile
import sys
import platform
import zipfile
import argparse
import sys
import time


class ProgressBar(object):
    """ProgressBar class holds the options of the progress bar.
    The options are:
        start   State from which start the progress. For example, if start is
                5 and the end is 10, the progress of this state is 50%
        end     State in which the progress has terminated.
        width   --
        fill    String to use for "filled" used to represent the progress
        blank   String to use for "filled" used to represent remaining space.
        format  Format
        incremental
    """
    def __init__(self, start=0, end=10, width=12, fill='=', blank='.', format='[%(fill)s>%(blank)s] %(progress)s%%', incremental=True):
        super(ProgressBar, self).__init__()

        self.start = start
        self.end = end
        self.width = width
        self.fill = fill
        self.blank = blank
        self.format = format
        self.incremental = incremental
        self.step = 100 / float(width) #fix
        self.reset()

    def __add__(self, increment):
        increment = self._get_progress(increment)
        if 100 > self.progress + increment:
            self.progress += increment
        else:
            self.progress = 100
        return self

    def __str__(self):
        progressed = int(self.progress / self.step) #fix
        fill = progressed * self.fill
        blank = (self.width - progressed) * self.blank
        return self.format % {'fill': fill, 'blank': blank, 'progress': int(self.progress)}

    __repr__ = __str__

    def _get_progress(self, increment):
        return float(increment * 100) / self.end

    def reset(self):
        """Resets the current progress to the start point"""
        self.progress = self._get_progress(self.start)
        return self


class AnimatedProgressBar(ProgressBar):
    """Extends ProgressBar to allow you to use it straighforward on a script.
    Accepts an extra keyword argument named `stdout` (by default use sys.stdout)
    and may be any file-object to which send the progress status.
    """
    def __init__(self, *args, **kwargs):
        super(AnimatedProgressBar, self).__init__(*args, **kwargs)
        self.stdout = kwargs.get('stdout', sys.stdout)

    def show_progress(self):
        if hasattr(self.stdout, 'isatty') and self.stdout.isatty():
            self.stdout.write('\r')
        else:
            self.stdout.write('\n')
        self.stdout.write(str(self))
        self.stdout.flush()



CWD = os.path.dirname(os.path.abspath(__file__))
BASE_DIR = os.path.join(CWD, ".smt_solvers")
PATHS = []


def get_python_version():
    return "%d.%d" % sys.version_info[0:2]

def get_architecture():
    return platform.machine()

def untar(fname, directory=".", mode='r:gz'):
    # open the tarfile and use the 'r:gz' parameter
    # the 'r:gz' mode enables gzip compression reading
    tfile = tarfile.open(fname, mode)
    tfile.extractall(directory)

def unzip(fname, directory="."):
    with zipfile.ZipFile(fname, "r") as myzip:
        myzip.extractall(directory)

def download(url, file_name):
    u = urllib2.urlopen(url)
    f = open(file_name, 'wb')
    meta = u.info()
    bar = None
    if len(meta.getheaders("Content-Length")) > 0:
        file_size = int(meta.getheaders("Content-Length")[0])
        print("Downloading: %s Bytes: %s" % (file_name, file_size))
        bar = AnimatedProgressBar(end=file_size, width=80)

    block_sz = 8192
    while True:
        buff = u.read(block_sz)
        if not buff:
            break

        f.write(buff)
        if len(meta.getheaders("Content-Length")) > 0:
            bar + len(buff)
            bar.show_progress()
    print ""
    f.close()


def install_msat(options):
    base_name =  "mathsat-5.2.12-linux-%s" % get_architecture()
    archive_name = "%s.tar.gz" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)

    if not os.path.exists(archive):
        download("http://mathsat.fbk.eu/download.php?file=%s" % archive_name, archive)

    untar(archive, BASE_DIR)

    os.system('cd %s/python; python setup.py build' % dir_path)

    PATHS.append("%s/python" % dir_path)
    PATHS.append("%s/build/lib.linux-%s-%s" % (dir_path, get_architecture(), get_python_version()))



def install_z3(options):
    base_name =  "z3"
    archive_name = "%s.zip" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)
    install_path = os.path.join(BASE_DIR, "z3_bin")

    if not os.path.exists(archive):
        download("http://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=z3&changeSetId=cee7dd39444c9060186df79c2a2c7f8845de415b", archive)

    unzip(archive, dir_path)
    if not os.path.exists(install_path):
        os.mkdir(install_path)
    os.system("cd %s; python scripts/mk_make.py --prefix=%s" % (dir_path, install_path))
    os.system("cd %s/build; make -j%d; make install" % (dir_path, options.make_j))

    PATHS.append("%s/lib/python2.7/dist-packages" % install_path)



def install_cvc4(options):
    git = "68f22235a62f5276b206e9a6692a85001beb8d42"
    base_name =  "CVC4-%s" % git
    archive_name = "%s.tar.gz" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)

    if not os.path.exists(archive):
        download("https://codeload.github.com/CVC4/CVC4/tar.gz/%s" % git, archive)

    untar(archive, BASE_DIR)
    os.system("cd %s; bash autogen.sh;" % dir_path)
    os.system("cd %s/contrib; bash get-antlr-3.4;" % dir_path)
    os.system("cd %s; \
    ./configure --enable-language-bindings=python \
                --with-antlr-dir=%s/antlr-3.4 ANTLR=%s/antlr-3.4/bin/antlr3;\
    make -j%d" % (dir_path, dir_path, dir_path, options.make_j))
    os.system("cd %s/builds/src/bindings/python; mv .libs/CVC4.so.3.0.0 ./_CVC4.so" % dir_path)

    PATHS.append("%s/builds/src/bindings/python" % dir_path)



def install_yices(options):
    base_name =  "yices-2.3.0"
    archive_name = "%s-%s-unknown-linux-gnu-static-gmp.tar.gz" % (base_name, get_architecture())
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)
    yices_path = os.path.join(BASE_DIR, "yices_bin")

    if not os.path.exists(archive):
        #http://yices.csl.sri.com/cgi-bin/yices2-newnewdownload.cgi?file=yices-2.3.0-x86_64-unknown-linux-gnu-static-gmp.tar.gz&accept=I+Agree
        download("http://yices.csl.sri.com/cgi-bin/yices2-newnewdownload.cgi?file=%s&accept=I+Agree" % archive_name, archive)

    untar(archive, BASE_DIR)
    if not os.path.exists(yices_path):
        os.mkdir(yices_path)
    os.system("cd %s; ./install-yices %s" % (dir_path, yices_path))

    pyices_git = "aa0b91c39aa00c19c2160e83aad822dc468ce328"
    pyices_base_name =  "pyices-%s" % pyices_git
    pyices_archive_name = "%s.tar.gz" % pyices_base_name
    pyices_archive = os.path.join(BASE_DIR, pyices_archive_name)
    pyices_dir_path = os.path.join(BASE_DIR, pyices_base_name)

    if not os.path.exists(pyices_archive):
        download("https://codeload.github.com/cheshire/pyices/tar.gz/%s" % pyices_git, pyices_archive)

    untar(pyices_archive, BASE_DIR)
    os.system("export YICES_PATH=\"%s\"; cd %s; python setup.py install --user" % (yices_path, pyices_dir_path))
    os.system('cd %s; python setup.py build' % pyices_dir_path)

    PATHS.append("%s/build/lib.linux-%s-%s" % (pyices_dir_path, get_architecture(), get_python_version()))



def install_pycudd(options):
    base_name =  "pycudd2.0.2"
    archive_name = "%s.tar.gz" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)

    if not os.path.exists(archive):
        download("http://bears.ece.ucsb.edu/ftp/pub/pycudd2.0/%s" % archive_name, archive)

    if os.path.exists(dir_path):
        os.system("rm -rf %s" % dir_path)
    untar(archive, BASE_DIR)
    os.system("cd %s; patch -p1 -i %s/patches/pycudd.patch" % (dir_path, CWD))
    # -j is not supported by this building system
    os.system("cd %s/cudd-2.4.2; ./setup.sh; make -f Makefile_64bit; make -f Makefile_64bit libso" % dir_path)
    os.system("cd %s/pycudd; make" % dir_path)

    PATHS.append("%s/pycudd" % dir_path)



def parse_options():
    parser = argparse.ArgumentParser(description='Install SMT Solvers')
    parser.add_argument('--z3', dest='z3', action='store_true',
                        default=False, help='Install Z3')
    parser.add_argument('--msat', dest='msat', action='store_true',
                        default=False, help='Install MathSAT')
    parser.add_argument('--cvc4', dest='cvc4', action='store_true',
                        default=False, help='Install CVC4')
    parser.add_argument('--yices', dest='yices', action='store_true',
                        default=False, help='Install Yices')
    parser.add_argument('--cudd', dest='cudd', action='store_true',
                        default=False, help='Install CUDD (pycudd)')
    parser.add_argument('--make-j', dest='make_j', metavar='N',
                        type=int, default=1,
                        help='Define paralellism for make (Default: 1)')
    parser.add_argument('--confirm-agreement', dest='skip_intro',
                        action='store_true', default=False,
                        help='Confirm that you agree with the licenses of the\
                        solvers and skip the interactive question')

    if len(sys.argv)==1:
        parser.print_help()
        sys.exit(1)

    options = parser.parse_args()
    return options


def print_welcome():
    msg = """\
This script allows you to install the solvers supported by pySMT.

By executing this script, you confirm that you have read and agreed
with the licenses of each solver.

Notice: the installation process might require building tools
        (e.g., make and gcc).
"""
    print(msg)
    res = raw_input("Continue? [Y]es/[N]o: ").lower()

    if res != "y":
        exit(-1)


def main():
    # create install folder if needed
    if not os.path.exists(BASE_DIR):
        os.mkdir(BASE_DIR)

    options = parse_options()
    if not options.skip_intro:
        print_welcome()

    if options.z3:
        install_z3(options)

    if options.cvc4:
        install_cvc4(options)

    if options.msat:
        install_msat(options)

    if options.yices:
        install_yices(options)

    if options.cudd:
        install_pycudd(options)

    print("\n")
    print("*" * 80)
    print("Add the following to your .bashrc file or to your environment:")
    print("export PYTHONPATH=\"$PYTHONPATH:"+ ":".join(PATHS) + "\"")



if __name__ == "__main__":
    main()
