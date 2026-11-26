# pySMT

Solver-agnostic Python library for SMT formulae (Python >= 3.10). The
development guide is `docs/development.rst`; this file summarizes it.

## Layout

- `src/pysmt/`: the package. `shortcuts.py` is the public entry point,
  `formula.py` the `FormulaManager`, `solvers/` the native solver wrappers,
  `smtlib/` the SMT-LIB parser and printers, `optimization/` the optimizers,
  `cmd/install.py` and `cmd/installers/` the `pysmt-install` command.
- `tests/`: the test suite (not shipped in the package). `TestCase` and the
  skip decorators are in `tests/__init__.py`, the example formulae in
  `tests/examples.py`, SMT-LIB benchmarks in `tests/smtlib/`.
- `examples/`: standalone scripts, run by the CI `all` job.
- `docs/`: Sphinx sources in `.rst` (the README is `.rst` too).
  `docs/code_snippets/*.py` are run by `tests/test_doc_snippets.py`.
- `ci/`: `bump_solvers.py` (weekly solver pin bump), `stamp_dev_version.py`
  (`.devN` versions on master), `cla.sh` (CONTRIBUTORS check).

## just recipes

- `just install`: `uv sync` (project and dev group). It removes solvers
  installed with `pysmt-install`, so reinstall them afterwards.
- `just test [ARGS]`: pytest without the `slow` tests, stopping at the first
  failure. `just test-all [ARGS]` includes the slow tests.
- `just lint`: `ruff check` and `ruff format --check`. `just format` applies
  the formatter and the safe fixes.
- `just typecheck`: mypy on `src/pysmt` and `tests` (configured in
  `pyproject.toml`).
- `just precommit`: all pre-commit hooks on the whole repo (Python >= 3.11).
- `just install-solver NAME [INSTALL_PATH]`: install a solver as the CI does
  and run `pysmt-install --check`. NAME can also be `all`, `none`,
  `z3_wrap` or `msat_wrap`.
- `just solver-updates`: report newer solver releases than the pins.
- `just build`, `just docs` (into `docs/_build/html`), `just bump VERSION`,
  `just clean`.

A single test: `just test tests/test_formula.py::TestFormulaManager::test_and_node`.

## Lint and types

The ruff rule families and their exceptions are in `pyproject.toml`
(`[tool.ruff.lint]`). Run ruff only on tracked files, since `just lint`
also checks untracked files under the linted directories:

    git ls-files -z '*.py' | xargs -0 uv run ruff check
    git ls-files -z '*.py' | xargs -0 uv run ruff format --check

## Solvers

`uv run pysmt-install --z3` installs a solver into `.venv` (with `uv pip`,
since the environment has no pip). `uv run pysmt-install --check` lists what
pySMT can find. `PYSMT_SOLVER="z3, msat"` limits the solvers visible to
pySMT and the tests. The pins are in `src/pysmt/cmd/install.py`; the PyPI
ones are bumped by the weekly `bump-solvers` workflow, MathSAT,
OptiMathSAT, `libyices` and PicoSAT by hand.

## Conventions

- Commit subjects end with the issue number, e.g. `Fix X (#873)`.
- Every user-visible change gets an entry in the unreleased section of
  `docs/CHANGES.rst`, ending with the issue or PR number.
- Commits produced by `ruff format` or `ruff check --fix` contain no manual
  edits and are listed in `.git-blame-ignore-revs`. PRs with such commits
  are merged with a merge commit (not squashed or rebased), so the hashes
  stay valid.
- The just recipes are documented in `docs/development.rst`, not in the
  README, which is also the PyPI page.
- New committers must be added to `CONTRIBUTORS` (checked by `ci/cla.sh`).
