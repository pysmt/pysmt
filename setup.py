from setuptools import setup, find_packages

setup(
    name='PySMT',
    version='0.3.0',
    author='PySMT Team',
    author_email='info@pysmt.org',
    packages = find_packages(),
    include_package_data = True,
    url='http://www.pysmt.org',
    license='APACHE',
    description='A library for SMT Formulae manipulation and solving',
    long_description=open('README.rst').read(),
    install_requires=["six"],
    entry_points={
        'console_scripts': [
            'pysmt = pysmt.cmd.shell:main',
            'pysmt-shell = pysmt.cmd.shell:main_interactive',
            'pysmt-install = pysmt.cmd.install:main',
        ],
    },
)
