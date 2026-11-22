set shell := ["bash", "-cu"]

# Paths checked by ruff (lint and format)
lint_paths := "src tests examples ci docs shell.py"

default:
    @just --list

# Sync the environment from uv.lock (project + dev group)
install:
    uv sync

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
