set shell := ["bash", "-cu"]

# On Windows, a plain "bash" can resolve to the WSL launcher in System32
set windows-shell := ["powershell.exe", "-NoLogo", "-NoProfile", "-Command"]

# Paths checked by ruff (lint and format)
lint_paths := "src tests examples ci docs shell.py"

# Default --install-path of pysmt-install
solvers_dir := home_directory() / ".smt_solvers"

default:
    @just --list

# Sync the environment from uv.lock (project + dev group)
install:
    uv sync

# Install solver NAME (a pysmt-install solver, all, none, z3_wrap or msat_wrap) and check it
[unix]
install-solver name install_path=solvers_dir:
    #!/usr/bin/env bash
    set -euo pipefail
    name="{{name}}"
    dir="{{install_path}}"
    bin=tests/smtlib/bin
    # tests/smtlib/test_generic_wrapper.py runs every tests/smtlib/bin/*.solver.sh
    wrap() { cp "$2" "$bin/$1"; cp "$bin/$1.solver.sh.template" "$bin/$1.solver.sh"; }
    mathsat() { find "$dir/msat" -path "*/bin/mathsat" -type f | head -n 1; }
    case "$name" in
        none) ;;
        z3_wrap|msat_wrap)
            # Keep the bindings out of the environment, so that pySMT sees only the wrapper
            target=$(mktemp -d)
            uv run pysmt-install "--${name%_wrap}" --target "$target" --confirm-agreement --install-path "$dir"
            if [ "$name" = z3_wrap ]; then wrap z3 "$target/bin/z3"; else wrap mathsat "$(mathsat)"; fi
            rm -rf "$target"
            ;;
        *)
            uv run pysmt-install "--$name" --confirm-agreement --install-path "$dir"
            uv run pysmt-install --check "--$name" --install-path "$dir"
            if [ "$name" = all ]; then
                # The z3-solver wheel installs the z3 executable in the environment
                wrap z3 "$(uv run python -c 'import shutil; print(shutil.which("z3"))')"
                wrap mathsat "$(mathsat)"
            fi
            ;;
    esac

# Install solver NAME (a pysmt-install solver, all or none) and check it
[windows]
install-solver name install_path=solvers_dir:
    {{ if name == "none" { "" } else { "uv run pysmt-install --" + name + " --confirm-agreement --install-path '" + install_path + "'" } }}
    uv run pysmt-install --check {{ if name == "none" { "" } else { "--" + name } }} --install-path '{{install_path}}'

# Report newer solver releases than the pysmt-install pins, without changing them
solver-updates:
    uv run python ci/bump_solvers.py --dry-run

# Run the tests not marked as slow, stopping at the first failure
test *args:
    uv run pytest -m "not slow" -x {{args}}

# Run all the tests, including the slow ones
test-all *args:
    uv run pytest -x {{args}}

# Run all lint and formatting checks. Fails if any issues are found.
lint:
    uv run ruff check {{lint_paths}}
    uv run ruff format --check {{lint_paths}}

# Apply the formatter and auto-fix lint issues where possible
format:
    uv run ruff format {{lint_paths}}
    uv run ruff check --fix {{lint_paths}}

# Static type checking
typecheck:
    uv run mypy

# Run all pre-commit hooks against the whole repo
precommit:
    uv run pre-commit run --all-files --show-diff-on-failure

# Build sdist + wheel
build:
    uv build

# Bump the version in pyproject.toml and refresh uv.lock
bump version:
    sed -i 's/^version = ".*"/version = "{{version}}"/' pyproject.toml
    uv lock
    @echo "Now: git commit -am 'Bump version to {{version}}'"

# Build the HTML documentation into docs/_build/html
docs:
    uv run --group docs sphinx-build -b html docs docs/_build/html

# Remove build, cache, and tooling artifacts
clean:
    rm -rf build/ dist/ docs/_build/ .mypy_cache/ .pytest_cache/ .ruff_cache/
