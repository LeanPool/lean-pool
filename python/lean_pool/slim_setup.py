"""Shrink Lake's per-module ``.setup.json`` compiler inputs to local imports.

Before compiling a module, Lake writes ``.lake/build/ir/<Module>.setup.json``
and passes it to ``lean --setup``. Its ``importArts`` field records absolute
artifact paths for every transitive import, so a module that imports Mathlib
carries about 3,000 entries (~1.6 MB). Across the pool that is ~46 GB of the
~69 GB build directory that every CI job restores, saves, and uploads.

Lake never reads these files back: it rewrites one whenever it recompiles that
module. Lean Pool's own readers (``validation_cache`` and the exposition
extractor) only use ``importArts`` keys that name a ``LeanPool`` module or a
Lean source in this checkout. Dropping every other key keeps their results
unchanged. Modification times are preserved, so ``find -newer`` packaging still
ships only freshly built files. Standard library only, so CI can run it with
the runner's ``python3``.
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import sys
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from pathlib import Path

LOGGER = logging.getLogger(__name__)
SETUP_SUFFIX = ".setup.json"


@dataclass(frozen=True)
class Outcome:
    """Sizes of one setup file before and after slimming."""

    before: int
    after: int
    rewritten: bool


def is_local(module: str, root: Path) -> bool:
    """Whether a reader of the inventory could map ``module`` to a pool source."""
    return (
        module.split(".")[0] == "LeanPool"
        or (root / (module.replace(".", "/") + ".lean")).is_file()
    )


def slim_inventory(inventory: dict, root: Path) -> dict | None:
    """Return the inventory without non-local imports, or ``None`` if unchanged."""
    imports = inventory.get("importArts")
    if not isinstance(imports, dict):
        return None
    kept = {module: arts for module, arts in imports.items() if is_local(module, root)}
    if len(kept) == len(imports):
        return None
    return inventory | {"importArts": kept}


def slim_file(path: Path, root: Path) -> Outcome:
    """Rewrite one setup file in place, keeping its access and modification times."""
    status = path.stat()
    try:
        slimmed = slim_inventory(json.loads(path.read_bytes()), root)
    except (OSError, ValueError) as error:
        LOGGER.warning("%s: left unchanged (%s)", path, error)
        return Outcome(status.st_size, status.st_size, rewritten=False)
    if slimmed is None:
        return Outcome(status.st_size, status.st_size, rewritten=False)
    temporary = path.with_name(path.name + ".slim")
    after = temporary.write_bytes(json.dumps(slimmed, separators=(",", ":")).encode())
    os.utime(temporary, ns=(status.st_atime_ns, status.st_mtime_ns))
    temporary.replace(path)
    return Outcome(status.st_size, after, rewritten=True)


def setup_files(build: Path) -> list[Path]:
    """Every Lake setup file under the build's ``ir`` directory."""
    directory = build / "ir"
    if not directory.is_dir():
        return []
    return sorted(directory.rglob("*" + SETUP_SUFFIX))


def _slim_in_worker(arguments: tuple[Path, Path]) -> Outcome:
    return slim_file(*arguments)


def slim_build(root: Path, workers: int | None = None) -> list[Outcome]:
    """Slim every setup file in ``root``'s pool build, in parallel."""
    paths = setup_files(root / ".lake/build")
    if not paths:
        return []
    with ProcessPoolExecutor(max_workers=workers or os.cpu_count()) as executor:
        return list(
            executor.map(
                _slim_in_worker, [(path, root) for path in paths], chunksize=64
            )
        )


def main(arguments: list[str] | None = None) -> int:
    """Slim the checkout's setup files and report the space saved."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--workers", type=int)
    options = parser.parse_args(arguments)
    logging.basicConfig(level=logging.INFO, format="slim-setup: %(message)s")
    outcomes = slim_build(options.repo.resolve(), options.workers)
    before = sum(outcome.before for outcome in outcomes)
    after = sum(outcome.after for outcome in outcomes)
    rewritten = sum(outcome.rewritten for outcome in outcomes)
    print(
        f"Slimmed {rewritten} of {len(outcomes)} Lake setup files: "
        f"{before / 1e9:.2f} GB -> {after / 1e9:.2f} GB."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
