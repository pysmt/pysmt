#from distutils.core import setup
from setuptools import setup, find_packages

setup(
    name='PySMT',
    version='0.2.3.dev',
    author='PySMT Team',
    author_email='info@pysmt.org',
    packages = find_packages(),
    include_package_data = True,
    # packages=['pysmt', 'pysmt.smtlib', 'pysmt.solvers',
    #           'pysmt.utils', 'pysmt.walkers',
    #           'pysmt.test', 'pysmt.test.smtlib'],
    url='http://www.pysmt.org',
    license='APACHE',
    description='A library for SMT Formulae manipulation and solving',
    long_description=open('README.rst').read(),
    entry_points={
        'console_scripts': [
            'pysmt = shell:main',
            'pysmt-shell = shell:main_interactive',
            'pysmt-install = install:main',
        ],
    },
)
