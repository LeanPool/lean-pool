"""Reuse successful project validation after compiling the current checkout.

CI restores receipts from main or earlier runs of the same PR. Every receipt
covers module inventories, transitive local imports, dependency pins, and code.
Static repository invariants and text style lint still run on every checkout.
Missed checks run as concurrent Lean processes; receipts and reported errors
keep the sequential check order.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import subprocess
import time
from collections.abc import Callable, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any

LOGGER = logging.getLogger(__name__)
SHARED_INPUTS = (
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "lakefile.lean",
    "scripts/ci/LeanPoolLinters.lean",
    "python/lean_pool/validation_cache.py",
    "python/pyproject.toml",
    "python/uv.lock",
    ".github/workflows/lean_action_ci.yml",
)
LINT_INPUTS = ("scripts/nolints.json", "scripts/ci/lint-project.lean")
QUALITY_INPUTS = (
    "scripts/nolints-style.txt",
    "python/lean_pool/quality.py",
    "python/lean_pool/registry.py",
    "python/lean_pool/indexes.py",
)
GLOBAL_INPUTS = SHARED_INPUTS + LINT_INPUTS + QUALITY_INPUTS
WORKERS_VARIABLE = "LEAN_POOL_VALIDATION_WORKERS"
# Each Lean check process is single-threaded with about 1 GB of private memory;
# imported .olean files are memory-mapped and shared between processes.
DEFAULT_WORKERS = 4


def validation_workers() -> int:
    """Return the number of concurrent Lean check processes to run."""
    configured = os.environ.get(WORKERS_VARIABLE)
    if configured:
        workers = int(configured)
        if workers < 1:
            raise ValueError(f"{WORKERS_VARIABLE} must be positive: {configured}")
        return workers
    return max(1, min(DEFAULT_WORKERS, os.cpu_count() or 1))


def run_ordered[T](tasks: Sequence[Callable[[], T]], workers: int) -> list[T]:
    """Run independent tasks concurrently and return their results in task order.

    The first task in order that raises re-raises here, after unstarted tasks are
    cancelled and running ones finish, exactly as a sequential loop would.
    """
    if workers <= 1 or len(tasks) <= 1:
        return [task() for task in tasks]
    with ThreadPoolExecutor(max_workers=workers) as executor:
        futures = [executor.submit(task) for task in tasks]
        try:
            return [future.result() for future in futures]
        except BaseException:
            for future in futures:
                future.cancel()
            raise


@dataclass(frozen=True)
class Check[T]:
    """One cacheable validation of a module group."""

    kind: str
    modules: list[str]
    validate: Callable[[], list[T]]
    metadata: Any = None


def checker_inputs(kind: str | None) -> tuple[str, ...]:
    """Track each check's implementation; unknown checks retain every input."""
    if kind == "lint":
        return SHARED_INPUTS + LINT_INPUTS
    if kind in {"axioms", "backdoors", "declarations"}:
        return SHARED_INPUTS + QUALITY_INPUTS
    return GLOBAL_INPUTS


def pool_units(root: Path) -> list[list[str]]:
    """Partition every pool source, including the root and unregistered modules."""
    units: dict[str, list[str]] = {}
    for path in sorted((root / "LeanPool").rglob("*.lean")):
        relative = path.relative_to(root).with_suffix("")
        unit = relative.parts[1]
        units.setdefault(unit, []).append(".".join(relative.parts))
    if (root / "LeanPool.lean").exists():
        units["__root__"] = ["LeanPool"]
    return [sorted(modules) for _, modules in sorted(units.items())]


def _module_sources(
    root: Path,
    module: str,
    imported_sources: dict[str, Path | None],
    *,
    discovered_sources: set[Path] | None = None,
) -> set[Path]:
    setup = root / (".lake/build/ir/" + module.replace(".", "/") + ".setup.json")
    inventory = json.loads(setup.read_text())
    if inventory["name"] != module or not isinstance(inventory["importArts"], dict):
        raise ValueError("invalid compiler inventory")
    paths = {root / (module.replace(".", "/") + ".lean")}
    for imported in inventory["importArts"]:
        if imported not in imported_sources:
            path = root / (imported.replace(".", "/") + ".lean")
            imported_sources[imported] = path if path.is_file() else None
        path = imported_sources[imported]
        if path is not None:
            paths.add(path)
            # Keep discoveries even if a later import makes this inventory fail.
            if discovered_sources is not None:
                discovered_sources.add(path)
        elif imported.split(".")[0] == "LeanPool":
            raise ValueError(f"missing imported source: {imported}")
    return paths


def source_inventory(
    root: Path,
    modules: list[str],
    *,
    inventories: dict[str, set[Path]] | None = None,
    imported_sources: dict[str, Path | None] | None = None,
) -> set[Path]:
    """Use every module's compiler inventory; fall back to all local Lean sources."""
    paths = {root / (module.replace(".", "/") + ".lean") for module in modules}
    inventories = {} if inventories is None else inventories
    imported_sources = {} if imported_sources is None else imported_sources
    try:
        for module in modules:
            if module not in inventories:
                inventories[module] = _module_sources(
                    root, module, imported_sources, discovered_sources=paths
                )
            paths.update(inventories[module])
    except (OSError, ValueError, KeyError, TypeError):
        LOGGER.warning(
            "%s: missing import inventory; hashing all local sources", modules[0]
        )
        paths.update((root / "LeanPool").rglob("*.lean"))
        index = root / "LeanPool.lean"
        if index.exists():
            paths.add(index)
    return paths


class ValidationCache:
    """Store pass receipts only, with content fingerprints and atomic publication."""

    def __init__(
        self,
        root: Path,
        directory: Path,
        *,
        refresh: bool = False,
        workers: int | None = None,
    ) -> None:
        """Load optional receipts; a missing or corrupt cache is a cold run."""
        self.root = root
        self.directory = directory
        self.refresh = refresh
        self.workers = validation_workers() if workers is None else workers
        self.digests: dict[Path, str] = {}
        # Compilation finishes before validation; reuse inventories and path
        # lookups only within this immutable checkout, never across CI runs.
        self.inventories: dict[str, set[Path]] = {}
        self.imported_sources: dict[str, Path | None] = {}
        self.fingerprint_inputs: dict[
            tuple[tuple[str, ...], tuple[str, ...]], dict[str, str]
        ] = {}
        self.receipts: dict[str, dict[str, Any]] = {}
        self.used: dict[str, dict[str, Any]] = {}
        self.hits = 0
        self.misses = 0
        try:
            data = json.loads((directory / "passes.json").read_text())
            if data["version"] == 1 and isinstance(data["receipts"], dict):
                self.receipts = data["receipts"]
        except (OSError, ValueError, KeyError, TypeError):
            pass

    def fingerprint(
        self, modules: list[str], metadata: Any = None, *, kind: str | None = None
    ) -> str:
        """Hash all checked inputs, retaining missing optional files in the key."""
        global_inputs = checker_inputs(kind)
        key = (tuple(modules), global_inputs)
        if key not in self.fingerprint_inputs:
            self.fingerprint_inputs[key] = self._fingerprint_inputs(
                modules, global_inputs
            )
        payload = {
            "inputs": self.fingerprint_inputs[key],
            "modules": modules,
            "metadata": metadata,
        }
        return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()

    def _fingerprint_inputs(
        self, modules: list[str], global_inputs: tuple[str, ...]
    ) -> dict[str, str]:
        paths = source_inventory(
            self.root,
            modules,
            inventories=self.inventories,
            imported_sources=self.imported_sources,
        )
        paths.update(self.root / name for name in global_inputs)
        inputs = {}
        for path in sorted(paths):
            if path not in self.digests:
                self.digests[path] = (
                    hashlib.sha256(path.read_bytes()).hexdigest()
                    if path.is_file()
                    else "missing"
                )
            inputs[path.relative_to(self.root).as_posix()] = self.digests[path]
        return inputs

    def check[T](
        self,
        kind: str,
        modules: list[str],
        validate: Callable[[], list[T]],
        metadata: Any = None,
    ) -> list[T]:
        """Run on a miss and retain only passes; failures never create receipts."""
        return self.check_all([Check(kind, modules, validate, metadata)], workers=1)[0]

    def check_all[T](
        self, checks: Sequence[Check[T]], *, workers: int | None = None
    ) -> list[list[T]]:
        """Run every missed check concurrently; return errors in check order.

        Fingerprints, hit/miss counts and receipts are computed and recorded on
        the calling thread, so worker threads only run the validators.
        """
        keys: list[str] = []
        expected: list[dict[str, Any]] = []
        missed: list[int] = []
        for index, check in enumerate(checks):
            digest = self.fingerprint(check.modules, check.metadata, kind=check.kind)
            keys.append(f"{check.kind}:{check.modules[0]}")
            expected.append(
                {"fingerprint": digest, "modules": check.modules, "passed": True}
            )
            if not self.refresh and self.receipts.get(keys[index]) == expected[index]:
                self.hits += 1
                LOGGER.info("%s: cache hit", keys[index])
            else:
                self.misses += 1
                missed.append(index)
        outcomes = run_ordered(
            [_timed(keys[index], checks[index].validate) for index in missed],
            self.workers if workers is None else workers,
        )
        results: list[list[T]] = [[] for _ in checks]
        for index, errors in zip(missed, outcomes, strict=True):
            results[index] = errors
        for index, errors in enumerate(results):
            if not errors:
                self.used[keys[index]] = expected[index]
        return results

    def save(self) -> None:
        """Publish only receipts used in this run, pruning deleted/changed projects."""
        self.directory.mkdir(parents=True, exist_ok=True)
        temporary = self.directory / "passes.tmp"
        temporary.write_text(json.dumps({"version": 1, "receipts": self.used}) + "\n")
        temporary.replace(self.directory / "passes.json")
        LOGGER.info(
            "Validation: %d cached checks, %d fresh checks", self.hits, self.misses
        )


def _timed[T](key: str, validate: Callable[[], list[T]]) -> Callable[[], list[T]]:
    def run() -> list[T]:
        LOGGER.info("%s: validating", key)
        start = time.monotonic()
        errors = validate()
        LOGGER.info(
            "%s: %s in %.1fs",
            key,
            "failed" if errors else "passed",
            time.monotonic() - start,
        )
        return errors

    return run


def _lint_unit(root: Path, modules: list[str]) -> list[str]:
    """Lint one unit; output is buffered so concurrent units stay readable."""
    process = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/ci/lint-project.lean", *modules],
        cwd=root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if process.returncode == 0:
        LOGGER.info("lint:%s: %s", modules[0], process.stdout.strip())
        return []
    return [
        f"{modules[0]}: lint failed with exit code {process.returncode}\n"
        + process.stdout.rstrip()
    ]


def lint_pool(root: Path, cache: ValidationCache) -> list[str]:
    """Lint owned declarations once per unit, importing every owned module."""
    checks = [
        Check("lint", modules, lambda modules=modules: _lint_unit(root, modules))
        for modules in pool_units(root)
    ]
    return [error for errors in cache.check_all(checks) for error in errors]


def main() -> int:
    """Run the cached declaration linter or repository quality checker."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("lint", "quality"))
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--cache", type=Path, default=Path(".lake/validation-cache/v1"))
    parser.add_argument("--refresh", action="store_true")
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="validation: %(message)s")
    root = arguments.repo.resolve()
    cache = ValidationCache(root, root / arguments.cache, refresh=arguments.refresh)
    if arguments.check == "lint":
        errors = lint_pool(root, cache)
        # Keep quality receipts for the subsequent step.
        cache.used = {
            key: receipt
            for key, receipt in cache.receipts.items()
            if not key.startswith("lint:")
        } | cache.used
    else:
        from lean_pool.quality import run_checks

        errors = run_checks(root, validation_cache=cache)
        cache.used |= {
            key: receipt
            for key, receipt in cache.receipts.items()
            if key.startswith("lint:")
        }
    for error in errors:
        print(error if isinstance(error, str) else error.format(root))
    if errors:
        return 1
    cache.save()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
