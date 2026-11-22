set shell := ["bash", "-cu"]

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

# Static type checking
typecheck:
    uv run mypy

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
    uvx --from sphinx sphinx-build -b html docs docs/_build/html

# Remove build, cache, and tooling artifacts
clean:
    rm -rf build/ dist/ docs/_build/ .mypy_cache/ .pytest_cache/
