set shell := ["bash", "-cu"]

default:
    @just --list

# Sync the environment from uv.lock (project + dev group)
install:
    uv sync

# Run the test suite
test *args:
    uv run pytest pysmt {{args}}

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

# Remove build, cache, and tooling artifacts
clean:
    rm -rf build/ dist/ .mypy_cache/ .pytest_cache/
