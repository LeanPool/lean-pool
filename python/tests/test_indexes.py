"""Check complete project coverage, safe regeneration and public exports."""

from pathlib import Path

import pytest

from lean_pool import indexes
from lean_pool.quality import _check_project_indexes
from lean_pool.rebase import main as rebase_main
from lean_pool.rebase import render_index, resolvable
from lean_pool.rebase_fastpath import check_index


def _sources(root: Path) -> None:
    """Create a single-file project and a project with nested source files."""
    (root / "LeanPool/Beta/Nested").mkdir(parents=True)
    for name in ("Alpha", "Beta", "Beta/Core", "Beta/Nested/Other"):
        (root / f"LeanPool/{name}.lean").write_text("module\n")
    (root / "lakefile.toml").write_text("requiresModuleSystem = true\n")


def _generate(root: Path) -> None:
    """Opt a fixture into the migrated layout using the production CLI."""
    assert (
        indexes.main(["--repo", str(root), "--project-roots", "--lib", "LeanPool"]) == 0
    )


def test_complete_public_indexes(tmp_path: Path) -> None:
    """Every source is covered once, including the original entry modules."""
    _sources(tmp_path)
    _generate(tmp_path)
    assert (tmp_path / "LeanPool.lean").read_text() == (
        indexes.MODULE_HEADER
        + "public import LeanPool.Alpha.Imports\n"
        + "public import LeanPool.Beta.Imports\n"
    )
    assert (tmp_path / "LeanPool/Beta/Imports.lean").read_text() == (
        indexes.AGGREGATE_HEADER
        + "public import LeanPool.Beta\n"
        + "public import LeanPool.Beta.Core\n"
        + "public import LeanPool.Beta.Nested.Other\n"
    )
    assert not (tmp_path / "Challenge.lean").exists()
    assert not (tmp_path / "Solution.lean").exists()
    assert indexes.structure_errors(tmp_path) == []
    assert _check_project_indexes(tmp_path) == []
    assert check_index(tmp_path)
    assert render_index(tmp_path) == (tmp_path / "LeanPool.lean").read_text()
    assert indexes.main(["--repo", str(tmp_path), "--lib", "LeanPool", "--check"]) == 0


@pytest.mark.parametrize(
    "damage", ["missing", "duplicate", "private", "foreign", "math"]
)
def test_rejects_incomplete_or_unsafe_aggregate(tmp_path: Path, damage: str) -> None:
    """The quality gate rejects broken public coverage and non-index code."""
    _sources(tmp_path)
    _generate(tmp_path)
    path = tmp_path / "LeanPool/Beta/Imports.lean"
    source = path.read_text()
    if damage == "missing":
        source = source.replace("public import LeanPool.Beta.Core\n", "")
    elif damage == "duplicate":
        source += "public import LeanPool.Beta.Core\n"
    elif damage == "private":
        source = source.replace("public import", "import", 1)
    elif damage == "foreign":
        source += "public import LeanPool.Alpha\n"
    else:
        source += "def unexpected := 1\n"
    path.write_text(source)
    assert _check_project_indexes(tmp_path)
    assert not check_index(tmp_path)
    assert indexes.main(["--repo", str(tmp_path), "--lib", "LeanPool", "--check"]) > 0
    assert path.read_text() == source


def test_rejects_flat_root_and_new_unlisted_source(tmp_path: Path) -> None:
    """Reachability alone cannot hide flat imports or incomplete project roots."""
    _sources(tmp_path)
    _generate(tmp_path)
    (tmp_path / "LeanPool/Beta/New.lean").write_text("module\n")
    assert _check_project_indexes(tmp_path)
    assert rebase_main(["index", "--repo", str(tmp_path)]) == 0
    assert _check_project_indexes(tmp_path) == []
    (tmp_path / "LeanPool.lean").write_text("public import LeanPool.Beta.New\n")
    assert _check_project_indexes(tmp_path)
    assert rebase_main(["index", "--repo", str(tmp_path)]) == 0
    assert _check_project_indexes(tmp_path) == []


def test_deleted_aggregates_cannot_restore_flat_layout(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """After rollout the gate remains mandatory even if every aggregate is deleted."""
    monkeypatch.setattr(indexes, "REQUIRE_PROJECT_ROOTS", True)
    _sources(tmp_path)
    (tmp_path / "LeanPool.lean").write_text("module\npublic import LeanPool.Alpha\n")
    assert _check_project_indexes(tmp_path)
    assert indexes.main(["--repo", str(tmp_path), "--lib", "LeanPool"]) == 0
    assert _check_project_indexes(tmp_path) == []


def test_preserves_existing_sources(tmp_path: Path) -> None:
    """An existing Imports.lean containing mathematics must never be overwritten."""
    _sources(tmp_path)
    path = tmp_path / "LeanPool/Beta/Imports.lean"
    source = "module\npublic def existing := 1\n"
    path.write_text(source)
    assert indexes.main(["--repo", str(tmp_path), "--project-roots"]) == 1
    assert path.read_text() == source


def test_mechanical_aggregate_conflict_resolution(tmp_path: Path) -> None:
    """Concurrent additions to the same project regenerate their shared root."""
    _sources(tmp_path)
    _generate(tmp_path)
    path = tmp_path / "LeanPool/Beta/Imports.lean"
    path.write_text("<<<<<<< HEAD\n" + path.read_text() + "=======\n>>>>>>> incoming\n")
    assert resolvable(["LeanPool.lean", "LeanPool/Beta/Imports.lean"])
    assert not resolvable(["LeanPool/Beta/Core.lean"])
    assert rebase_main(["index", "--repo", str(tmp_path)]) == 0
    assert _check_project_indexes(tmp_path) == []


def test_generator_does_not_delete_declarations(tmp_path: Path) -> None:
    """A generated marker cannot authorize overwriting added mathematical code."""
    _sources(tmp_path)
    _generate(tmp_path)
    path = tmp_path / "LeanPool/Beta/Imports.lean"
    source = path.read_text() + "public def unexpected := 1\n"
    path.write_text(source)
    assert indexes.main(["--repo", str(tmp_path), "--lib", "LeanPool"]) == 1
    assert path.read_text() == source


def test_lean_public_exports(tmp_path: Path) -> None:
    """A consumer sees entry and nested declarations through only LeanPool."""
    import os
    import shutil
    import subprocess

    lean = shutil.which("lean")
    if lean is None:
        pytest.skip("Lean toolchain not installed")
    (tmp_path / "LeanPool/Example/Nested").mkdir(parents=True)
    sources = {
        "LeanPool/Example/Leaf.lean": (
            "module\npublic def answer : Nat := 42\n"
            "public theorem leafFact : (1 : Nat) = 1 := rfl\n"
        ),
        "LeanPool/Example.lean": (
            "module\nimport LeanPool.Example.Leaf\n"
            "public def rootAnswer : Nat := answer\n"
        ),
        "LeanPool/Example/Nested/Other.lean": (
            "module\npublic def nestedAnswer : Nat := 7\n"
        ),
    }
    for name, source in sources.items():
        (tmp_path / name).write_text(source)
    _generate(tmp_path)
    (tmp_path / "Consumer.lean").write_text(
        "module\nimport LeanPool\n"
        "public def consumer : Nat := answer + rootAnswer + nestedAnswer\n"
        "example : (1 : Nat) = 1 := leafFact\n"
    )
    modules = [
        *sources,
        "LeanPool/Example/Imports.lean",
        "LeanPool.lean",
        "Consumer.lean",
    ]
    for name in modules:
        subprocess.run(
            [lean, "-o", str(Path(name).with_suffix(".olean")), name],
            cwd=tmp_path,
            env={**os.environ, "LEAN_PATH": str(tmp_path)},
            check=True,
            capture_output=True,
            timeout=30,
        )


def test_default_generation_only_writes_pool_indexes(tmp_path: Path) -> None:
    """Default regeneration never recreates retired library roots."""
    _sources(tmp_path)
    assert indexes.main(["--repo", str(tmp_path), "--module"]) == 0
    assert (tmp_path / "LeanPool.lean").exists()
    assert not (tmp_path / "Challenge.lean").exists()
    assert not (tmp_path / "Solution.lean").exists()
