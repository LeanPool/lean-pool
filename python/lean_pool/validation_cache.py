"""Reuse successful project validation after compiling the current checkout.

CI restores receipts from main or earlier runs of the same PR. Every receipt
covers module inventories, transitive local imports, dependency pins, and code.
Static repository invariants and text style lint still run on every checkout.

Build shards can validate their own projects in parallel (``shard``) and hand
their pass receipts to the assembling job (``merge``). That job still recomputes
every fingerprint and runs whatever a shard did not pass, so it alone decides.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import subprocess
from collections.abc import Callable
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


def checker_inputs(kind: str | None) -> tuple[str, ...]:
    """Track each check's implementation; unknown checks retain every input."""
    if kind == "lint":
        return SHARED_INPUTS + LINT_INPUTS
    if kind in {"axioms", "backdoors", "declarations"}:
        return SHARED_INPUTS + QUALITY_INPUTS
    return GLOBAL_INPUTS


def unit_name(module: str) -> str:
    """The pool unit that owns a module; the root index is its own unit."""
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else "__root__"


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


def read_receipts(path: Path) -> dict[str, dict[str, Any]]:
    """Read a receipts file; a missing or corrupt one holds no receipts."""
    try:
        data = json.loads(path.read_text())
        if data["version"] == 1 and isinstance(data["receipts"], dict):
            return data["receipts"]
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return {}


def write_receipts(directory: Path, receipts: dict[str, dict[str, Any]]) -> None:
    """Publish a receipts file atomically."""
    directory.mkdir(parents=True, exist_ok=True)
    temporary = directory / "passes.tmp"
    temporary.write_text(json.dumps({"version": 1, "receipts": receipts}) + "\n")
    temporary.replace(directory / "passes.json")


class ValidationCache:
    """Store pass receipts only, with content fingerprints and atomic publication."""

    def __init__(
        self,
        root: Path,
        directory: Path,
        *,
        refresh: bool = False,
        units: frozenset[str] | None = None,
    ) -> None:
        """Load optional receipts; a missing or corrupt cache is a cold run.

        With ``units``, checks of every other unit are skipped without a receipt.
        """
        self.root = root
        self.directory = directory
        self.refresh = refresh
        self.units = units
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
        self.receipts = read_receipts(directory / "passes.json")

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
        if self.units is not None and unit_name(modules[0]) not in self.units:
            return []
        digest = self.fingerprint(modules, metadata, kind=kind)
        key = f"{kind}:{modules[0]}"
        expected = {"fingerprint": digest, "modules": modules, "passed": True}
        if not self.refresh and self.receipts.get(key) == expected:
            self.hits += 1
            self.used[key] = expected
            LOGGER.info("%s: cache hit", key)
            return []
        self.misses += 1
        LOGGER.info("%s: validating", key)
        errors = validate()
        if not errors:
            self.used[key] = expected
        return errors

    def save(self) -> None:
        """Publish only receipts used in this run, pruning deleted/changed projects."""
        write_receipts(self.directory, self.used)
        LOGGER.info(
            "Validation: %d cached checks, %d fresh checks", self.hits, self.misses
        )


def lint_pool(
    root: Path, cache: ValidationCache, *, keep_going: bool = False
) -> list[str]:
    """Lint owned declarations once per unit, importing every owned module.

    A failing unit raises, unless ``keep_going`` asks for its name instead.
    """
    failed = []
    for modules in pool_units(root):

        def validate() -> list[str]:
            process = subprocess.run(
                [
                    "lake",
                    "env",
                    "lean",
                    "--run",
                    "scripts/ci/lint-project.lean",
                    *modules,
                ],
                cwd=root,
                check=not keep_going,
            )
            return [modules[0]] if process.returncode else []

        failed.extend(cache.check("lint", modules, validate))
    return failed


def validate_shard(root: Path, cache: ValidationCache) -> bool:
    """Lint and audit only the cache's units, keeping every pass they earn.

    This runs the per-project checks of the whole-pool run through the same
    functions. Repository-wide invariants stay with the assembling job.
    """
    from lean_pool.quality import _cached_pool_audits, _check_projects

    failed = lint_pool(root, cache, keep_going=True)
    for unit in failed:
        print(f"lint failed: {unit}")
    errors = _check_projects(root, cache) + _cached_pool_audits(root, cache)
    for error in errors:
        print(error.format(root))
    cache.save()
    return not (failed or errors)


def merge_receipts(directory: Path, fragments: list[Path]) -> int:
    """Add shards' pass receipts to the cache; return how many were added.

    Each fragment is a receipts file or a directory of downloaded ones.

    A receipt only counts where the assembling job computes the same
    fingerprint for the same modules, so merging cannot certify other inputs.
    """
    receipts = read_receipts(directory / "passes.json")
    added = 0
    files = [
        file
        for fragment in fragments
        for file in (
            sorted(fragment.rglob("passes.json")) if fragment.is_dir() else [fragment]
        )
    ]
    for fragment in files:
        for key, receipt in read_receipts(fragment).items():
            if isinstance(receipt, dict) and receipts.get(key) != receipt:
                receipts[key] = receipt
                added += 1
    write_receipts(directory, receipts)
    return added


def main() -> int:
    """Run the cached declaration linter or repository quality checker."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("lint", "quality", "shard", "merge"))
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--cache", type=Path, default=Path(".lake/validation-cache/v1"))
    parser.add_argument("--refresh", action="store_true")
    parser.add_argument("--units", nargs="*", default=[])
    parser.add_argument("fragments", nargs="*", type=Path)
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="validation: %(message)s")
    root = arguments.repo.resolve()
    if arguments.check == "merge":
        added = merge_receipts(root / arguments.cache, arguments.fragments)
        LOGGER.info("Merged %d shard receipts", added)
        return 0
    if arguments.check == "shard":
        cache = ValidationCache(
            root,
            root / arguments.cache,
            refresh=arguments.refresh,
            units=frozenset(arguments.units),
        )
        return 0 if validate_shard(root, cache) else 1
    cache = ValidationCache(root, root / arguments.cache, refresh=arguments.refresh)
    if arguments.check == "lint":
        lint_pool(root, cache)
        # Keep quality receipts for the subsequent step.
        cache.used = {
            key: receipt
            for key, receipt in cache.receipts.items()
            if not key.startswith("lint:")
        } | cache.used
        errors = []
    else:
        from lean_pool.quality import run_checks

        errors = run_checks(root, validation_cache=cache)
        cache.used |= {
            key: receipt
            for key, receipt in cache.receipts.items()
            if key.startswith("lint:")
        }
    for error in errors:
        print(error.format(root))
    if errors:
        return 1
    cache.save()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
