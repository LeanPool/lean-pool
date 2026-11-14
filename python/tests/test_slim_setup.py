"""Check that slimming Lake setup files keeps every local reader's result."""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from lean_pool.exposition.extract import project_sources
from lean_pool.slim_setup import main, slim_build, slim_file
from lean_pool.validation_cache import source_inventory

ARTS = [["/runner/.lake/build/lib/lean/X.olean"], ["/runner/.lake/build/ir/X.ir"]]
IMPORTS = (
    "Init.Prelude",
    "Mathlib.Order.Basic",
    "LeanPool.A.Detail",
    "LeanPool.Gone",
    "Local.Helper",
)


def _setup_path(root: Path, module: str) -> Path:
    return root / (".lake/build/ir/" + module.replace(".", "/") + ".setup.json")


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """A pool project importing Mathlib, a pool module, and a non-pool local file."""
    for module in ("LeanPool", "LeanPool.A", "LeanPool.A.Detail", "Local.Helper"):
        path = tmp_path / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"-- {module}\n")
    setup = _setup_path(tmp_path, "LeanPool.A")
    setup.parent.mkdir(parents=True, exist_ok=True)
    setup.write_text(
        json.dumps(
            {
                "name": "LeanPool.A",
                "isModule": True,
                "importArts": dict.fromkeys(IMPORTS, ARTS),
            },
            indent=2,
        )
    )
    os.utime(setup, ns=(1_000_000_000, 2_000_000_000))
    return tmp_path


def _readers(root: Path) -> tuple[set[Path], set[Path]]:
    validation = source_inventory(root, ["LeanPool.A"])
    exposition = project_sources(root, "A")
    return validation, exposition


def test_slimming_keeps_only_local_imports(repository: Path) -> None:
    """Dependency entries and artifact paths go; local import names stay."""
    setup = _setup_path(repository, "LeanPool.A")
    outcome = slim_file(setup, repository)
    inventory = json.loads(setup.read_text())
    assert outcome.rewritten and outcome.after < outcome.before
    assert list(inventory["importArts"]) == [
        "LeanPool.A.Detail",
        "LeanPool.Gone",
        "Local.Helper",
    ]
    assert inventory["importArts"]["Local.Helper"] == []
    assert inventory["name"] == "LeanPool.A" and inventory["isModule"] is True


def test_readers_see_the_same_sources(repository: Path) -> None:
    """Validation and exposition inventories, including errors, are unchanged."""
    inventory = json.loads(_setup_path(repository, "LeanPool.A").read_text())
    del inventory["importArts"]["LeanPool.Gone"]
    _setup_path(repository, "LeanPool.A").write_text(json.dumps(inventory))
    before = _readers(repository)
    slim_build(repository, workers=1)
    assert _readers(repository) == before
    assert repository / "Local/Helper.lean" in before[0]


def test_modification_time_is_preserved(repository: Path) -> None:
    """Shard packaging selects files by mtime, so slimming must not touch it."""
    setup = _setup_path(repository, "LeanPool.A")
    slim_file(setup, repository)
    assert setup.stat().st_mtime_ns == 2_000_000_000
    assert not setup.with_name(setup.name + ".slim").exists()


def test_slimming_is_idempotent(repository: Path) -> None:
    """A second pass finds nothing to drop and leaves the file alone."""
    setup = _setup_path(repository, "LeanPool.A")
    slim_file(setup, repository)
    content = setup.read_bytes()
    assert not slim_file(setup, repository).rewritten
    assert setup.read_bytes() == content


def test_unreadable_files_are_left_alone(repository: Path) -> None:
    """A truncated file stays as it is; readers already fall back on it."""
    setup = _setup_path(repository, "LeanPool.A")
    setup.write_text("{")
    assert not slim_file(setup, repository).rewritten
    assert setup.read_text() == "{"


def test_command_reports_savings(
    repository: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """The CLI slims the whole build and prints a one-line summary."""
    assert main(["--repo", str(repository), "--workers", "1"]) == 0
    assert "Slimmed 1 of 1 Lake setup files" in capsys.readouterr().out


def test_missing_build_is_a_no_op(tmp_path: Path) -> None:
    """Jobs that restored nothing still succeed."""
    assert slim_build(tmp_path) == []
