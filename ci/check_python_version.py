import platform
import sys
import re

def main():
    if len(sys.argv) != 2:
        print('Usage: %s <expected-python-version>' % sys.argv[0])
        exit(1)

    expected_impl = None
    expected_major = None
    expected_minor = None

    expected_version_string = sys.argv[1]
    match = re.match(r'^(\d+)\.(\d+)$', expected_version_string)
    if match is not None:
        expected_impl = 'CPython'
        expected_major = match.group(1)
        expected_minor = match.group(2)

    match = re.match(r'^(\d+)\.(\d+).\d+$', expected_version_string)
    if match is not None:
        expected_impl = 'CPython'
        expected_major = match.group(1)
        expected_minor = match.group(2)

    if expected_version_string == 'pypy':
        expected_impl = 'PyPy'
        expected_major = '2'
        expected_minor = '7'

    if expected_version_string == 'pypy3':
        expected_impl = 'PyPy'
        expected_major = '3'
        expected_minor = '*'

    match = re.match(r'^pypy(\d+)\.(\d+).*?$', expected_version_string)
    if match is not None:
        expected_impl = 'PyPy'
        expected_major = match.group(1)
        expected_minor = match.group(2)

    if expected_impl is None:
        print('Unknown python version specified: %s' % expected_version_string)
        exit(1)

    impl = platform.python_implementation()
    version = sys.version_info

    if impl != expected_impl:
        print('Wrong platform detected. %s was expected, but this script ' \
              'is running on %s!' % (expected_impl, impl))
        exit(2)
    if (expected_minor != '*' and expected_minor != str(version.minor)) or \
       expected_major != str(version.major):
        print('Wrong version detected. %s.%s was expected, but this script ' \
              'is running on %s.%s!' % (expected_major, expected_minor,
                                        version.major, version.minor))
        exit(2)

    print('All OK. The detected python version is %s %s.%s' % \
          (impl, version.major, version.minor))

if __name__ == '__main__':
    main()
