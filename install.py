#!/usr/bin/env python

# Copyright 2015 Andrea Micheli and Marco Gario
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


BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOG = []

def log(msg):
    LOG.append(msg)

def short_python_version():
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
    if len(meta.getheaders("Content-Length")) > 0:
        file_size = int(meta.getheaders("Content-Length")[0])
        print("Downloading: %s Bytes: %s" % (file_name, file_size))


    file_size_dl = 0
    block_sz = 8192
    while True:
        buff = u.read(block_sz)
        if not buff:
            break

        file_size_dl += len(buff)
        f.write(buff)
        if len(meta.getheaders("Content-Length")) > 0:
            status = r"%10d  [%3.2f%%]" % (file_size_dl, file_size_dl * 100. / file_size)
            status = status + chr(8)*(len(status)+1)
            print status,
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

    log("Install done, add the following to enable mathsat")
    log("export PYTHONPATH=\"$PYTHONPATH:%s/python:%s/python/build/lib.linux-x86_64-2.7\"" %\
        (dir_path, dir_path))


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

    # os.system('cd %s/python; python setup.py build' % dir_path)

    log("Install done, add the following to enable z3")
    log("export PYTHONPATH=\"$PYTHONPATH:%s/lib/python2.7/dist-packages\"" % install_path)


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

    log("Install done, add the following to enable cvc4")
    log("export PYTHONPATH=\"$PYTHONPATH:%s/builds/src/bindings/python\"" % dir_path)


def install_yices(options):
    raise NotImplementedError
    base_name =  "yices-2.2.2"
    archive_name = "%s-%s-unknown-linux-gnu-static-gmp.tar.gz" % (base_name, get_architecture())
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)

    if not os.path.exists(archive):
        download("http://yices.csl.sri.com/cgi-bin/yices2-newnewdownload.cgi?file=%s&accept=I+accept" % archive_name, archive)

    untar(archive, BASE_DIR)
    os.system("cd %s; ./install-yices ../" % base_name)

    pyices_git = "aa0b91c39aa00c19c2160e83aad822dc468ce328"
    pyices_base_name =  "pyices-%s" % pyices_git
    pyices_archive_name = "%s.tar.gz" % pyices_base_name
    pyices_archive = os.path.join(BASE_DIR, pyices_archive_name)
    pyices_dir_path = os.path.join(BASE_DIR, pyices_base_name)

    if not os.path.exists(pyices_archive):
        download("https://codeload.github.com/cheshire/pyices/tar.gz/%s" % pyices_git, pyices_archive)

    untar(pyices_archive, BASE_DIR)
    os.system("export YICES_PATH=\"%s\"; cd %s; python setup.py install --user" % (dir_path, pyices_dir_path))
    # os.system('cd %s/python; python setup.py build' % dir_path)

    # print "Install done, add the following to enable mathsat"
    # print "export PYTHONPATH=\"$PYTHONPATH:%s/python:%s/python/build/lib.linux-x86_64-2.7\"" %\
    #     (dir_path, dir_path)

def install_cudd(options):
    raise NotImplementedError


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
        insatll_pycudd(options)

    print("\n".join(LOG))

if __name__ == "__main__":
    main()
