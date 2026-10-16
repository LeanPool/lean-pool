"""Exercise checkpoint recovery, dependency ordering and publication boundaries."""

from __future__ import annotations

import json
import sqlite3
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from lean_pool import documentation


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Provide local modules with an import order different from their filenames."""
    (tmp_path / "LeanPool").mkdir()
    (tmp_path / "docbuild").mkdir()
    (tmp_path / "LeanPool.lean").write_text("module\n")
    (tmp_path / "LeanPool" / "A.lean").write_text(
        "module\npublic import all LeanPool.Z\n"
        "/- public import LeanPool.A -/\n"
        'def text := "import LeanPool.A"\n'
    )
    (tmp_path / "LeanPool" / "Z.lean").write_text("module\n")
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        (tmp_path / name).write_text("pinned\n")
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        (tmp_path / "docbuild" / name).write_text("pinned\n")
    return tmp_path


def populate(build: Path, value: str = "previous") -> None:
    """Write a real consistent SQLite database and its corresponding marker."""
    build.mkdir(parents=True, exist_ok=True)
    with sqlite3.connect(build / "api-docs.db") as connection:
        connection.execute("CREATE TABLE IF NOT EXISTS contents (value TEXT)")
        connection.execute("DELETE FROM contents")
        connection.execute("INSERT INTO contents VALUES (?)", (value,))
    (build / "doc-data").mkdir(exist_ok=True)
    (build / "doc-data" / "module.doc").write_text(value)


def test_import_order_ignores_comments_and_strings(repository: Path) -> None:
    """A project aggregate cannot trigger its entire cold closure in one batch."""
    modules = documentation.ordered_modules(repository)
    assert modules.index("LeanPool.Z") < modules.index("LeanPool.A")
    assert set(modules) == {"LeanPool", "LeanPool.A", "LeanPool.Z"}
    assert documentation.external_modules(repository) == ["Init", "Lake", "Lean", "Std"]


@pytest.mark.parametrize(
    "error", [RuntimeError("failed"), subprocess.TimeoutExpired("lake", 1)]
)
def test_failed_batch_restores_database_and_markers(tmp_path: Path, error) -> None:
    """A failed process must not leave half-updated data paired with valid markers."""
    populate(tmp_path)
    with pytest.raises(type(error)), documentation.batch_checkpoint(tmp_path):
        populate(tmp_path, "incomplete")
        (tmp_path / "doc-data" / "extra.doc").write_text("incomplete")
        raise error
    with sqlite3.connect(tmp_path / "api-docs.db") as connection:
        assert connection.execute("SELECT value FROM contents").fetchall() == [
            ("previous",)
        ]
    assert (tmp_path / "doc-data" / "module.doc").read_text() == "previous"
    assert not (tmp_path / "doc-data" / "extra.doc").exists()
    documentation.validate_database(tmp_path)


def test_first_failed_batch_leaves_no_checkpoint(tmp_path: Path) -> None:
    """An interrupted bootstrap must never look like an existing valid database."""
    with pytest.raises(RuntimeError), documentation.batch_checkpoint(tmp_path):
        populate(tmp_path)
        raise RuntimeError("failed")
    assert not (tmp_path / "api-docs.db").exists()
    assert not (tmp_path / "doc-data").exists()


def test_resume_skips_verified_batches_but_rechecks_changed_sources(
    repository: Path, monkeypatch
) -> None:
    """Only the same source and policy snapshot may reuse the saved cursor."""
    commands = []

    def build(command, directory, timeout):
        commands.append(command)
        populate(directory / ".lake" / "build")

    monkeypatch.setattr(documentation, "run_build", build)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert len(commands) == 2
    documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert len(commands) == 2
    (repository / "LeanPool" / "Z.lean").write_text("module\n-- changed\n")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert len(commands) == 4
    monkeypatch.setenv("DOCGEN_DEPS_DOCS_URL", "https://example.com/new-docs")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)


def test_timeout_advances_only_completed_batches(repository: Path, monkeypatch) -> None:
    """Timeout recovery keeps the prior batch and resumes at the interrupted target."""
    calls = 0

    def build(command, directory, timeout):
        nonlocal calls
        calls += 1
        populate(directory / ".lake" / "build", str(calls))
        if calls == 2:
            raise subprocess.TimeoutExpired(command, timeout)

    monkeypatch.setattr(documentation, "run_build", build)
    assert not documentation.build_batches(repository, "lake", 60, 2)
    build_path = repository / "docbuild" / ".lake" / "build"
    assert json.loads((build_path / documentation.STATE).read_text())["cursor"] == 2
    assert (build_path / "doc-data" / "module.doc").read_text() == "1"
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert calls == 3


@pytest.mark.parametrize("failed_parent", [False, True])
def test_native_build_failure_stops_child_writers(
    tmp_path: Path, failed_parent: bool
) -> None:
    """A descendant cannot modify the restored checkpoint after its parent is killed."""
    script = tmp_path / "parent.py"
    result = tmp_path / "late-write"
    child = (
        "import time,pathlib; time.sleep(1); "
        "pathlib.Path('late-write').write_text('bad')"
    )
    script.write_text(
        "import subprocess,sys,time\n"
        f"subprocess.Popen([sys.executable, '-c', {child!r}])\n"
        + ("sys.exit(1)\n" if failed_parent else "time.sleep(60)\n")
    )
    error = (
        subprocess.CalledProcessError if failed_parent else subprocess.TimeoutExpired
    )
    with pytest.raises(error):
        documentation.run_build([sys.executable, str(script)], tmp_path, 0.2)
    subprocess.run([sys.executable, "-c", "import time; time.sleep(1.1)"], check=True)
    assert not result.exists()


def test_site_requires_every_module_and_excludes_dependencies(repository: Path) -> None:
    """A root-only site or accidental Mathlib tree cannot pass publication checks."""
    site = repository / "docbuild" / ".lake" / "build" / "doc"
    for name in ("index.html", "declarations/declaration-data.bmp", "LeanPool.html"):
        path = site / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("content")
    with pytest.raises(ValueError, match="missing documentation pages"):
        documentation.validate_site(repository)
    for name in ("A", "Z"):
        (site / "LeanPool").mkdir(exist_ok=True)
        (site / "LeanPool" / f"{name}.html").write_text("content")
    documentation.validate_site(repository)
    (site / "Mathlib").mkdir()
    with pytest.raises(ValueError, match="unexpected dependency"):
        documentation.validate_site(repository)


@pytest.mark.parametrize(
    "result,previous,phase,expected",
    [
        ("success", "false", "analysis", True),
        ("failure", "false", "analysis", False),
        ("cancelled", "false", "analysis", False),
        ("skipped", "true", "analysis", True),
        ("skipped", "false", "analysis", False),
        ("skipped", "true", "render", False),
    ],
)
def test_reused_analysis_propagates_completion(
    tmp_path: Path, result: str, previous: str, phase: str, expected: bool
) -> None:
    """Propagate completed stages and reject failures or unintended skips."""
    workflow = Path(__file__).resolve().parents[2] / ".github/workflows/docs-build.yml"
    command = yaml.safe_load(workflow.read_text())["jobs"]["receipt"]["steps"][0]["run"]
    output = tmp_path / "output"
    process = subprocess.run(
        ["bash", "-c", command],
        env={
            "RESULT": result,
            "PREVIOUS": previous,
            "PHASE": phase,
            "COMPLETE": "true",
            "GITHUB_OUTPUT": str(output),
        },
        capture_output=True,
    )
    assert (process.returncode == 0) == expected
    if expected:
        assert output.read_text() == "complete=true\n"
