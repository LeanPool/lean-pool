"""Lint and audit one build shard's projects, keeping every pass they earn.

A shard job runs this for the projects it built, in parallel with the other
shards, and uploads the resulting pass receipts. It runs the per-project checks
of the whole-pool run through the same functions. Repository-wide invariants,
and the decision itself, stay with the assembling job: it merges the receipts
(``validation_cache merge``), recomputes every fingerprint, and runs whatever
has no matching pass.
"""

from __future__ import annotations

import argparse
import logging
from pathlib import Path

from lean_pool.quality import _cached_pool_audits, _check_projects
from lean_pool.validation_cache import ValidationCache, lint_pool

LOGGER = logging.getLogger(__name__)


def validate_shard(root: Path, cache: ValidationCache) -> bool:
    """Lint and audit only the cache's units; save their passes either way."""
    failed = lint_pool(root, cache)
    for error in failed:
        print(error)
    errors = _check_projects(root, cache) + _cached_pool_audits(root, cache)
    for error in errors:
        print(error.format(root))
    cache.save()
    return not (failed or errors)


def main(arguments: list[str] | None = None) -> int:
    """Validate the named units and report whether all of them passed."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--cache", type=Path, default=Path(".lake/validation-cache/v1"))
    parser.add_argument("--units", nargs="*", default=[])
    options = parser.parse_args(arguments)
    logging.basicConfig(level=logging.INFO, format="validation: %(message)s")
    root = options.repo.resolve()
    cache = ValidationCache(root, root / options.cache, units=frozenset(options.units))
    return 0 if validate_shard(root, cache) else 1


if __name__ == "__main__":
    raise SystemExit(main())
