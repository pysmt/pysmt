"""Stamp the dev version into pyproject.toml before a master build.

X.Y.Z.devM becomes X.Y.Z.devN, with N = total commit count on HEAD (monotonic,
independent of tags). No +gSHA local suffix: PyPI rejects local versions.
Release versions (no .dev suffix) are left untouched. Run only in CI; the
patched file is never committed.
"""

import pathlib
import re
import subprocess

py = pathlib.Path("pyproject.toml")
n = subprocess.check_output(["git", "rev-list", "--count", "HEAD"], text=True).strip()
text, count = re.subn(
    r'^(version = "\d+\.\d+\.\d+)\.dev\d+"',
    rf'\1.dev{n}"',
    py.read_text(),
    count=1,
    flags=re.M,
)
py.write_text(text)
print(f"stamped .dev{n}" if count else "release version, not stamped")
