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
        "module\nimport all LeanPool.Z\n"
        "/- public import LeanPool.A -/\n"
        'def text := "import LeanPool.A"\n'
    )
    (tmp_path / "LeanPool" / "Z.lean").write_text("module\n")
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        (tmp_path / name).write_text("pinned\n")
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        (tmp_path / "docbuild" / name).write_text("pinned\n")
    for module, imports in (
        ("LeanPool", {}),
        ("LeanPool.A", {"LeanPool.Z": {}, "Mathlib.Logic.Basic": {}}),
        ("LeanPool.Z", {}),
    ):
        inventory(tmp_path, module, imports)
    return tmp_path


def inventory(root: Path, module: str, imports: dict) -> None:
    """Write Lake's transitive import inventory for one module."""
    path = root / documentation.IR / (module.replace(".", "/") + ".setup.json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"name": module, "importArts": imports}))


def populate(build: Path, value: str = "previous", modules: tuple = ()) -> None:
    """Write a consistent SQLite database shaped like doc-gen's, with a marker."""
    build.mkdir(parents=True, exist_ok=True)
    with sqlite3.connect(build / "api-docs.db") as connection:
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("CREATE TABLE IF NOT EXISTS contents (value TEXT)")
        connection.execute("CREATE TABLE IF NOT EXISTS modules (name TEXT PRIMARY KEY)")
        connection.execute(
            "CREATE TABLE IF NOT EXISTS name_info (module_name TEXT NOT NULL, "
            "FOREIGN KEY (module_name) REFERENCES modules(name) ON DELETE CASCADE)"
        )
        connection.execute("DELETE FROM contents")
        connection.execute("INSERT INTO contents VALUES (?)", (value,))
        for name in modules:
            connection.execute("INSERT OR IGNORE INTO modules VALUES (?)", (name,))
            connection.execute("INSERT INTO name_info VALUES (?)", (name,))
    connection.close()
    (build / "doc-data").mkdir(exist_ok=True)
    (build / "doc-data" / "module.doc").write_text(value)


def compile_modules(root: Path, digest: str = "0", *modules: str) -> None:
    """Write Lake's compiled-module content hashes for the named modules."""
    for module in modules or tuple(documentation.module_sources(root)):
        path = (
            root / documentation.COMPILED / (module.replace(".", "/") + ".olean.hash")
        )
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(digest)


def recording_build(commands: list):
    """Stand in for Lake: record each batch and store its modules in the database."""

    def build(command, directory, timeout):
        commands.append(command)
        names = tuple(
            item.removeprefix("+").removesuffix(":docInfo") for item in command[2:]
        )
        populate(directory / ".lake" / "build", modules=names)

    return build


def test_import_order_ignores_comments_and_strings(repository: Path) -> None:
    """A project aggregate cannot trigger its entire cold closure in one batch."""
    modules = documentation.ordered_modules(repository)
    assert modules.index("LeanPool.Z") < modules.index("LeanPool.A")
    assert set(modules) == {"LeanPool", "LeanPool.A", "LeanPool.Z"}
    assert documentation.external_modules(repository) == ["Init", "Lake", "Lean", "Std"]


def test_render_builds_uncached_dependencies(repository: Path) -> None:
    """Tau Ceti has no olean cache, so rendering must compile what it links to."""
    (repository / "LeanPool" / "Z.lean").write_text(
        "module\n"
        "public import TauCeti.LinearAlgebra.Dual.Rank\n"
        "import Mathlib.Logic.Basic\n"
    )
    assert documentation.compiled_dependencies(repository) == [
        "Mathlib.Logic.Basic",
        "TauCeti.LinearAlgebra.Dual.Rank",
    ]


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


def test_resume_rechecks_only_changed_projects(repository: Path, monkeypatch) -> None:
    """An edit sends its project and importers back to Lake; shared inputs reset all."""
    commands: list = []
    monkeypatch.setattr(documentation, "run_build", recording_build(commands))
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert len(commands) == 2
    documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert len(commands) == 2
    (repository / "LeanPool" / "Z.lean").write_text("module\n-- changed\n")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert commands[2:] == [
        ["lake", "build", "+LeanPool.Z:docInfo", "+LeanPool.A:docInfo"]
    ]
    documentation.require_complete(repository)
    monkeypatch.setenv("DOCGEN_DEPS_DOCS_URL", "https://example.com/new-docs")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert len(commands[3:]) == 1 and len(commands[3]) == 5


def test_option_edit_reuses_projects_with_unchanged_compiled_modules(
    repository: Path, monkeypatch
) -> None:
    """Pool options reach pages only through compiled modules, so hash those instead."""
    commands: list = []
    monkeypatch.setattr(documentation, "run_build", recording_build(commands))
    compile_modules(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    (repository / "lakefile.toml").write_text("changed options\n")
    documentation.require_complete(repository)
    compile_modules(repository, "1", "LeanPool.A")
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert commands[1:] == [["lake", "build", "+LeanPool.A:docInfo"]]


@pytest.mark.parametrize("contents", [None, "broken", '{"name": "LeanPool.Z"}'])
def test_missing_inventory_hashes_the_whole_pool(
    repository: Path, monkeypatch, contents
) -> None:
    """Without Lake's import inventory, any pool edit re-checks the project."""
    path = repository / documentation.IR / "LeanPool/A.setup.json"
    if contents is None:
        path.unlink()
    else:
        path.write_text(contents)
    commands: list = []
    monkeypatch.setattr(documentation, "run_build", recording_build(commands))
    assert documentation.build_batches(repository, "lake", 60, 3)
    (repository / "LeanPool.lean").write_text("module\n-- changed\n")
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert commands[1:] == [
        ["lake", "build", "+LeanPool:docInfo", "+LeanPool.A:docInfo"]
    ]


def test_option_edit_without_compiled_hashes_rechecks_everything(
    repository: Path, monkeypatch
) -> None:
    """Missing Lake hashes conservatively tie every project to the pool options."""
    commands: list = []
    monkeypatch.setattr(documentation, "run_build", recording_build(commands))
    assert documentation.build_batches(repository, "lake", 60, 3)
    (repository / "lakefile.toml").write_text("changed options\n")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert len(commands) == 2 and len(commands[1]) == 5


def test_deleted_modules_leave_the_database_and_markers(
    repository: Path, monkeypatch
) -> None:
    """A removed module cannot keep a page, and its return is analyzed again."""
    commands: list = []
    monkeypatch.setattr(documentation, "run_build", recording_build(commands))
    assert documentation.build_batches(repository, "lake", 60, 3)
    build = repository / "docbuild" / ".lake" / "build"
    populate(build, modules=("Mathlib.Logic.Basic",))
    (build / "doc-data" / "LeanPool.Z.doc").write_text("marker")
    (build / "doc-data" / "LeanPool.Z.doc.trace").write_text("trace")
    (repository / "LeanPool" / "Z.lean").unlink()
    (repository / "LeanPool" / "A.lean").write_text("module\n")
    assert documentation.build_batches(repository, "lake", 60, 3)
    with sqlite3.connect(build / "api-docs.db") as connection:
        modules = {name for (name,) in connection.execute("SELECT name FROM modules")}
        orphans = connection.execute(
            "SELECT COUNT(*) FROM name_info WHERE module_name = 'LeanPool.Z'"
        ).fetchone()
    assert modules == {"LeanPool", "LeanPool.A", "Mathlib.Logic.Basic"}
    assert orphans == (0,)
    assert not list((build / "doc-data").glob("LeanPool.Z.doc*"))
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
    progress = json.loads((build_path / documentation.STATE).read_text())
    assert len(progress["projects"]) == 2
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
