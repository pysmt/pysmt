"""Bump the PyPI-backed solver pins of pysmt-install.

Rewrites the pins in src/pysmt/cmd/install.py to the latest PyPI releases and
reports newer MathSAT, OptiMathSAT, Yices and pyPicoSAT releases, which stay
manual bumps (their installers also encode archive names). Prints a Markdown
summary, used as the body of the bump PR. With --dry-run nothing is written.
"""

import argparse
import json
import os
import pathlib
import re
import urllib.error
import urllib.request

from pysmt.cmd.install import SOLVERS, PipSolver

INSTALL_PY = pathlib.Path(__file__).parents[1] / "src/pysmt/cmd/install.py"


def fetch(url, method="GET"):
    req = urllib.request.Request(url, method=method)
    token = os.environ.get("GH_TOKEN")
    if token and url.startswith("https://api.github.com/"):
        req.add_header("Authorization", f"Bearer {token}")
    return urllib.request.urlopen(req, timeout=30)


def pypi_latest(name):
    with fetch(f"https://pypi.org/pypi/{name}/json") as r:
        return json.load(r)["info"]["version"]


def exists(url):
    try:
        with fetch(url, "HEAD"):
            return True
    except urllib.error.HTTPError:
        return False


def as_tuple(version):
    return tuple(int(x) for x in version.split("."))


def mathsat_latest():
    with fetch("https://mathsat.fbk.eu/download.html") as r:
        html = r.read().decode()
    # Raises if the page no longer links any archive, so a layout change fails the run
    return max(re.findall(r"release/mathsat-(\d+(?:\.\d+)+)-", html), key=as_tuple)


def successors(version):
    """Next patch, minor and major version: 1.7.5 -> 1.7.6, 1.8.0, 2.0.0."""
    # OptiMathSAT's download pages lag behind its releases (1.7.5 is not listed),
    # so probe the archives instead. ponytail: misses a release that skips a number.
    parts = [int(x) for x in version.split(".")]
    for i in reversed(range(len(parts))):
        bumped = parts[:i] + [parts[i] + 1] + [0] * (len(parts) - i - 1)
        yield ".".join(map(str, bumped))


def newer_archive(version, url_template):
    return next(
        (v for v in successors(version) if exists(url_template.format(v=v))), None
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--dry-run", action="store_true", help="report only, do not rewrite pins"
    )
    args = parser.parse_args()

    solvers = {s.name: s for s in SOLVERS}
    yices, pico = solvers["yices"], solvers["picosat"]

    # (PyPI project, pinned version, text of the pin in install.py)
    pins = [
        (name, version, f'"{name}=={{v}}"')
        for s in SOLVERS
        if isinstance(s, PipSolver)
        for name, version in (r.split("==") for r in s.requirements)
    ]
    pins.append(
        ("yices", yices.extra_params["yices_api_version"], '"yices_api_version": "{v}"')
    )

    text = INSTALL_PY.read_text()
    bumped = []
    for name, current, pattern in pins:
        latest = pypi_latest(name)
        if latest != current:
            old, new = pattern.format(v=current), pattern.format(v=latest)
            assert text.count(old) == 1, f"{old} must occur once in {INSTALL_PY}"
            text = text.replace(old, new)
            bumped.append(f"- `{name}` {current} → {latest}")

    manual = []
    msat = mathsat_latest()
    if as_tuple(msat) > as_tuple(solvers["msat"].version):
        manual.append(f"- MathSAT {msat} (pinned {solvers['msat'].version})")
    optimsat = newer_archive(
        solvers["optimsat"].version,
        "https://optimathsat.disi.unitn.it/releases/optimathsat-{v}/"
        "optimathsat-{v}-linux-x86_64.tar.gz",
    )
    if optimsat:
        manual.append(
            f"- OptiMathSAT {optimsat} (pinned {solvers['optimsat'].version})"
        )
    with fetch("https://api.github.com/repos/SRI-CSL/yices2/releases/latest") as r:
        yices_latest = json.load(r)["tag_name"].removeprefix("yices-")
    if yices_latest != yices.version:
        manual.append(f"- Yices {yices_latest} (pinned {yices.version})")
    pico_current = f"{pico.version}.{pico.extra_params['pypicosat_minor_version']}"
    pico_latest = pypi_latest("pyPicoSAT")
    if pico_latest != pico_current:
        manual.append(f"- pyPicoSAT {pico_latest} (pinned {pico_current})")

    if bumped:
        print("Bumped the solver pins of `pysmt-install`:\n")
        print("\n".join(bumped) + "\n")
        if not args.dry_run:
            INSTALL_PY.write_text(text)
    if manual:
        print("Newer releases that need a manual bump:\n")
        print("\n".join(manual) + "\n")
    if not bumped and not manual:
        print("All solver pins are up to date.")


if __name__ == "__main__":
    main()
