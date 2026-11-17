"""Check validation coverage, dependency invalidation, and pass-only cache reuse."""

from __future__ import annotations

import json
import subprocess
import sys
import threading
import time
from pathlib import Path
from unittest.mock import patch

import pytest

from lean_pool.quality import _cached_pool_audits
from lean_pool.validation_cache import (
    GLOBAL_INPUTS,
    WORKERS_VARIABLE,
    Check,
    ValidationCache,
    _module_sources,
    lint_pool,
    main,
    pool_units,
    run_ordered,
    source_inventory,
    validation_workers,
)


def _inventory(root: Path, module: str, imports: tuple[str, ...] = ()) -> None:
    path = root / (".lake/build/ir/" + module.replace(".", "/") + ".setup.json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"name": module, "importArts": dict.fromkeys(imports)}))


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Create independent units, a nested module, and compiler import inventories."""
    for module in ("LeanPool", "LeanPool.A", "LeanPool.A.Detail", "LeanPool.B"):
        path = tmp_path / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"-- {module}\n")
        _inventory(tmp_path, module)
    _inventory(tmp_path, "LeanPool", ("LeanPool.A", "LeanPool.A.Detail", "LeanPool.B"))
    for name in GLOBAL_INPUTS:
        if name in {"lakefile.lean", "scripts/nolints.json"}:
            continue
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("configuration\n")
    return tmp_path


def _run(root: Path, *, refresh: bool = False) -> tuple[ValidationCache, list[str]]:
    cache = ValidationCache(root, root / ".lake/validation-cache/v1", refresh=refresh)
    calls: list[str] = []
    for modules in pool_units(root):
        cache.check("lint", modules, lambda: calls.append(modules[0]) or [])
    cache.save()
    return cache, calls


def test_coverage_and_warm_reuse(repository: Path) -> None:
    """Every file belongs to a unit, even without a registry or umbrella import."""
    units = pool_units(repository)
    covered = [module for modules in units for module in modules]
    assert sorted(covered) == [
        "LeanPool",
        "LeanPool.A",
        "LeanPool.A.Detail",
        "LeanPool.B",
    ]
    assert len(_run(repository)[1]) == 3
    assert _run(repository)[1] == []
    assert len(_run(repository, refresh=True)[1]) == 3


def test_project_edit_leaves_sibling_cached(repository: Path) -> None:
    """A rebase reuses identical sources regardless of commit SHA or registry order."""
    _run(repository)
    (repository / "LeanPool/projects.yml").write_text("projects: []\n")
    assert _run(repository)[1] == []
    (repository / "LeanPool/A/Detail.lean").write_text("-- edited nested source\n")
    assert _run(repository)[1] == ["LeanPool.A", "LeanPool"]


def test_transitive_import_of_nested_module_invalidates_consumer(
    repository: Path,
) -> None:
    """Dependencies of each nested module count, not just umbrella dependencies."""
    _inventory(repository, "LeanPool.A.Detail", ("LeanPool.B",))
    _run(repository)
    (repository / "LeanPool/B.lean").write_text("-- dependency edit\n")
    assert len(_run(repository)[1]) == 3


@pytest.mark.parametrize("name", GLOBAL_INPUTS)
def test_checker_edits_invalidate_only_dependent_checks(
    repository: Path, name: str
) -> None:
    """Unrelated tooling edits preserve passes; shared inputs invalidate all kinds."""
    kinds = ("lint", "axioms", "backdoors", "declarations", "future-check")
    directory = repository / ".lake/validation-cache/v1"
    cache = ValidationCache(repository, directory)
    for kind in kinds:
        for modules in pool_units(repository):
            cache.check(kind, modules, lambda: [])
    cache.save()
    (repository / name).write_text("changed\n")
    cache = ValidationCache(repository, directory)
    calls: list[tuple[str, str]] = []
    for kind in kinds:
        for modules in pool_units(repository):
            cache.check(kind, modules, lambda: calls.append((kind, modules[0])) or [])
    if name in {
        "python/lean_pool/quality.py",
        "scripts/nolints-style.txt",
        "python/lean_pool/registry.py",
        "python/lean_pool/indexes.py",
    }:
        fresh_kinds = ("axioms", "backdoors", "declarations", "future-check")
    elif name in {"scripts/ci/lint-project.lean", "scripts/nolints.json"}:
        fresh_kinds = ("lint", "future-check")
    else:
        fresh_kinds = kinds
    assert calls == [
        (kind, modules[0]) for kind in fresh_kinds for modules in pool_units(repository)
    ]
    assert len(calls) >= 3


@pytest.mark.parametrize("kind", ("lint", "axioms", "backdoors", "declarations"))
def test_source_changes_invalidate_every_check_kind(
    repository: Path, kind: str
) -> None:
    """Scoping checker inputs must preserve all imported-source dependencies."""
    directory = repository / ".lake/validation-cache/v1"
    cache = ValidationCache(repository, directory)
    for modules in pool_units(repository):
        cache.check(kind, modules, lambda: [])
    cache.save()
    (repository / "LeanPool/A/Detail.lean").write_text("-- changed\n")
    cache = ValidationCache(repository, directory)
    calls: list[str] = []
    for modules in pool_units(repository):
        cache.check(kind, modules, lambda: calls.append(modules[0]) or [])
    assert calls == ["LeanPool.A", "LeanPool"]


def test_quality_check_kinds_reuse_source_comparisons(repository: Path) -> None:
    """Quality checks sharing dependencies calculate their input list once."""
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    with patch.object(
        cache, "_fingerprint_inputs", wraps=cache._fingerprint_inputs
    ) as inputs:
        for kind in ("axioms", "backdoors", "declarations"):
            cache.check(kind, ["LeanPool.A"], lambda: [])
        assert inputs.call_count == 1


@pytest.mark.parametrize("contents", [None, "{", "{}", '{"name": "wrong"}'])
def test_missing_inventory_falls_back_conservatively(
    repository: Path, contents
) -> None:
    """A missing/broken nested inventory must not produce a false cache hit."""
    path = repository / ".lake/build/ir/LeanPool/A/Detail.setup.json"
    if contents is None:
        path.unlink()
    else:
        path.write_text(contents)
    _run(repository)
    (repository / "LeanPool/B.lean").write_text("-- changed\n")
    assert len(_run(repository)[1]) == 3


def test_metadata_is_scoped_to_one_project(repository: Path) -> None:
    """Changing one card's declaration list invalidates that check only."""
    modules = ["LeanPool.A"]
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    cache.check("declarations", modules, lambda: [], {"main_declarations": ["a"]})
    cache.save()
    cache = ValidationCache(repository, cache.directory)
    assert cache.check(
        "declarations", modules, lambda: ["error"], {"main_declarations": ["b"]}
    ) == ["error"]


def test_failures_and_corrupt_receipts_are_rechecked(repository: Path) -> None:
    """Failed validators and malformed saved data cannot create successful hits."""
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    assert cache.check("lint", ["LeanPool.A"], lambda: ["bad proof"]) == ["bad proof"]
    cache.save()
    assert _run(repository)[0].misses == 3
    (cache.directory / "passes.json").write_text("broken")
    assert _run(repository)[0].misses == 3


def test_added_deleted_sources_change_coverage(repository: Path) -> None:
    """New files are checked and deleted units are removed from the cache."""
    _run(repository)
    (repository / "LeanPool/B.lean").unlink()
    (repository / "LeanPool/C.lean").write_text("-- new project\n")
    _inventory(repository, "LeanPool.C")
    _inventory(repository, "LeanPool", ("LeanPool.A", "LeanPool.C"))
    cache, calls = _run(repository)
    assert calls == ["LeanPool.C", "LeanPool"]
    assert "lint:LeanPool.B" not in cache.used


def test_quality_audits_cover_every_owned_module(repository: Path) -> None:
    """Cold and warm checks preserve complete axiom/backdoor coverage."""
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    with (
        patch("lean_pool.quality._audit_axioms", return_value=[]) as axioms,
        patch("lean_pool.quality._run_option_audit", return_value=[]) as backdoors,
    ):
        assert _cached_pool_audits(repository, cache) == []
        # Audits run concurrently, so compare coverage rather than call order.
        assert sorted(call.args[1] for call in axioms.call_args_list) == sorted(
            pool_units(repository)
        )
        assert sorted(
            call.kwargs["only_modules"] for call in backdoors.call_args_list
        ) == sorted(pool_units(repository))
        cache.save()
        cache = ValidationCache(repository, cache.directory)
        assert _cached_pool_audits(repository, cache) == []
        assert axioms.call_count == backdoors.call_count == 3


def test_overlapping_checks_reuse_inventories_without_changing_fingerprints(
    repository: Path,
) -> None:
    """Shared imports are resolved once, while metadata still changes the key."""
    _inventory(repository, "LeanPool.A", ("LeanPool.A.Detail", "Mathlib.Shared"))
    _inventory(repository, "LeanPool.A.Detail", ("Mathlib.Shared",))
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    groups = [["LeanPool.A"], ["LeanPool.A", "LeanPool.A.Detail"]]
    checks = [
        (modules, metadata)
        for modules in groups
        for metadata in (None, {"main_declarations": ["a"]})
    ]
    expected = [
        ValidationCache(repository, cache.directory).fingerprint(modules, metadata)
        for modules, metadata in checks
    ]
    with patch(
        "lean_pool.validation_cache._module_sources",
        wraps=_module_sources,
    ) as inventories:
        assert [
            cache.fingerprint(modules, metadata) for modules, metadata in checks
        ] == expected
        assert inventories.call_count == 2
    assert expected[0] != expected[1]
    assert cache.imported_sources["Mathlib.Shared"] is None
    assert (
        source_inventory(repository, groups[1])
        == cache.inventories["LeanPool.A"] | cache.inventories["LeanPool.A.Detail"]
    )


def test_local_import_outside_pool_invalidates_cached_checks(repository: Path) -> None:
    """Memoized import lookups still cover local modules outside LeanPool."""
    source = repository / "Support.lean"
    source.write_text("def support := 1\n")
    _inventory(repository, "LeanPool.A.Detail", ("Support",))
    _run(repository)
    source.write_text("def support := 2\n")
    assert _run(repository)[1] == ["LeanPool.A"]


def test_missing_pool_import_falls_back_after_memoized_lookup(repository: Path) -> None:
    """A cached missing path cannot hide a missing imported pool source."""
    _inventory(repository, "LeanPool.A", ("LeanPool.Missing",))
    _inventory(repository, "LeanPool.A.Detail", ("LeanPool.Missing",))
    _run(repository)
    (repository / "LeanPool/B.lean").write_text("-- unrelated edit\n")
    assert len(_run(repository)[1]) == 3


@pytest.mark.parametrize("kind", ("lint", "axioms", "backdoors", "declarations"))
def test_inventory_fallback_preserves_discovered_external_dependencies(
    repository: Path, kind: str
) -> None:
    """An inventory error cannot hide a local dependency discovered before it."""
    source = repository / "Aux/Support.lean"
    source.parent.mkdir()
    source.write_text("def support := 1\n")
    _inventory(repository, "LeanPool.A.Detail", ("Aux.Support", "LeanPool.Missing"))
    directory = repository / ".lake/validation-cache/v1"
    modules = ["LeanPool.A", "LeanPool.A.Detail"]
    cache = ValidationCache(repository, directory)
    assert cache.check(kind, modules, lambda: []) == []
    cache.save()
    cache = ValidationCache(repository, directory)
    assert cache.check(kind, modules, lambda: ["unexpected recheck"]) == []
    cache.save()
    source.write_text("def support := 2\n")
    cache = ValidationCache(repository, directory)
    assert cache.check(kind, modules, lambda: ["changed dependency"]) == [
        "changed dependency"
    ]


def test_validation_workers_default_and_override(monkeypatch) -> None:
    """Workers default to at most four and can be configured, never to zero."""
    monkeypatch.delenv(WORKERS_VARIABLE, raising=False)
    assert 1 <= validation_workers() <= 4
    monkeypatch.setenv(WORKERS_VARIABLE, "2")
    assert validation_workers() == 2
    assert ValidationCache(Path("."), Path("missing")).workers == 2
    monkeypatch.setenv(WORKERS_VARIABLE, "0")
    with pytest.raises(ValueError, match="must be positive"):
        validation_workers()


def test_run_ordered_runs_concurrently_and_keeps_task_order() -> None:
    """Tasks overlap (the barrier needs all three) yet results keep task order."""

    def task(value: int, delay: float, barrier: threading.Barrier):
        def run() -> int:
            barrier.wait()
            time.sleep(delay)
            return value

        return run

    barrier = threading.Barrier(3, timeout=10)
    tasks = [task(0, 0.2, barrier), task(1, 0.1, barrier), task(2, 0.0, barrier)]
    assert run_ordered(tasks, workers=3) == [0, 1, 2]
    barrier = threading.Barrier(2, timeout=0.2)
    with pytest.raises(threading.BrokenBarrierError):
        run_ordered([task(0, 0.0, barrier)] * 2, workers=1)


def test_run_ordered_raises_first_failure_in_task_order() -> None:
    """A later task failing first cannot change which failure is reported."""
    later_failed = threading.Event()

    def first() -> None:
        assert later_failed.wait(10)
        raise RuntimeError("first")

    def later() -> None:
        later_failed.set()
        raise RuntimeError("later")

    with pytest.raises(RuntimeError, match="first"):
        run_ordered([first, later], workers=2)


def test_parallel_checks_match_sequential_receipts(repository: Path) -> None:
    """Concurrent validation records the same errors, receipts, and counts."""
    units = pool_units(repository)
    main_thread = threading.current_thread()
    validator_threads: set[threading.Thread] = set()

    def validator(kind: str, modules: list[str], delay: float):
        def run() -> list[str]:
            validator_threads.add(threading.current_thread())
            time.sleep(delay)
            return ["bad"] if (kind, modules[0]) == ("axioms", "LeanPool.B") else []

        return run

    def checks() -> list[Check[str]]:
        return [
            Check(kind, modules, validator(kind, modules, 0.05 * (6 - position)))
            for position, (kind, modules) in enumerate(
                (kind, modules) for kind in ("axioms", "backdoors") for modules in units
            )
        ]

    sequential = ValidationCache(repository, repository / "sequential", workers=1)
    expected = [
        sequential.check(check.kind, check.modules, check.validate)
        for check in checks()
    ]
    validator_threads.clear()
    parallel = ValidationCache(repository, repository / "parallel", workers=4)
    original_fingerprint = parallel.fingerprint

    def fingerprint(*arguments, **keywords):
        assert threading.current_thread() is main_thread
        return original_fingerprint(*arguments, **keywords)

    with patch.object(parallel, "fingerprint", side_effect=fingerprint):
        assert parallel.check_all(checks()) == expected
    assert expected == [[], ["bad"], [], [], [], []]
    assert main_thread not in validator_threads
    assert list(parallel.used.items()) == list(sequential.used.items())
    assert (parallel.hits, parallel.misses) == (0, 6)
    parallel.save()
    warm = ValidationCache(repository, parallel.directory, workers=4)
    assert warm.check_all(checks()) == expected
    assert (warm.hits, warm.misses) == (5, 1)


def test_lint_pool_reports_every_failed_unit_in_order(repository: Path) -> None:
    """Lint units run one at a time and every failure is reported in order."""
    commands: list[list[str]] = []

    def run(command: list[str], **keywords) -> subprocess.CompletedProcess:
        commands.append(command)
        modules = command[5:]
        failed = modules[0] in {"LeanPool", "LeanPool.B"}
        output = f"{modules[0]}: finding\n" if failed else "Lint passed.\n"
        return subprocess.CompletedProcess(command, int(failed), output)

    cache = ValidationCache(repository, repository / "cache", workers=3)
    with patch("lean_pool.validation_cache.subprocess.run", side_effect=run):
        errors = lint_pool(repository, cache)
    assert errors == [
        "LeanPool.B: lint failed with exit code 1\nLeanPool.B: finding",
        "LeanPool: lint failed with exit code 1\nLeanPool: finding",
    ]
    assert [command[5:] for command in commands] == pool_units(repository)
    assert list(cache.used) == ["lint:LeanPool.A"]


def test_lint_command_fails_without_saving_receipts(
    repository: Path, monkeypatch, capsys
) -> None:
    """A lint failure exits non-zero, prints the finding, and saves nothing."""
    monkeypatch.setattr(
        sys, "argv", ["validation_cache", "lint", "--repo", str(repository)]
    )
    failure = subprocess.CompletedProcess([], 1, "A.lean:1:1: error: finding\n")
    with patch("lean_pool.validation_cache.subprocess.run", return_value=failure):
        assert main() == 1
    assert "A.lean:1:1: error: finding" in capsys.readouterr().out
    assert not (repository / ".lake/validation-cache/v1/passes.json").exists()
