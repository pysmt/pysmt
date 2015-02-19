from distutils.core import setup

setup(
    name='PySMT',
    version='0.2.2',
    author='PySMT Team',
    author_email='',
    packages=['pysmt', 'pysmt.smtlib', 'pysmt.solvers',
              'pysmt.utils', 'pysmt.walkers',
              'pysmt.test', 'pysmt.test.smtlib'],
    url='http://www.pysmt.org',
    license='LICENSE',
    description='A library for SMT Formulae manipulation and solving',
    long_description=open('README.rst').read(),
    install_requires=[ ],
)
