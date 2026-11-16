"""Exercise bounded analysis, checkpoint recovery and publication boundaries."""

from __future__ import annotations

import json
import logging
import sqlite3
import subprocess
import sys
import threading
import time
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
    """Write a consistent SQLite database shaped like doc-gen's."""
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


def compile_modules(
    root: Path,
    digest: str = "0",
    *modules: str,
    artifact: str = "olean",
    cache_hash: bool = True,
) -> None:
    """Write real artifact presence and optional Lake content-hash sidecars."""
    for module in modules or tuple(documentation.module_sources(root)):
        path = (
            root / documentation.COMPILED / (module.replace(".", "/") + f".{artifact}")
        )
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"compiled {digest}\n")
        cached = Path(f"{path}.hash")
        if cache_hash:
            cached.write_text(digest)
        else:
            cached.unlink(missing_ok=True)


class RecordingAnalyzer:
    """Stand in for doc-gen: record each module and store it in the database."""

    def __init__(self, root: Path, fail: str | None = None) -> None:
        """Analyze into the repository's checkpoint, failing on one chosen module."""
        self.build = root / "docbuild" / ".lake" / "build"
        self.fail = fail
        self.modules: list[str] = []
        self.running = self.peak = 0
        self.lock = threading.Lock()

    def analyze(self, module: str) -> None:
        """Count simultaneous analyses and commit the module's records."""
        with self.lock:
            self.modules.append(module)
            self.running += 1
            self.peak = max(self.peak, self.running)
        try:
            if module == self.fail:
                raise subprocess.CalledProcessError(1, ["doc-gen4", "single", module])
            time.sleep(0.01)
            with self.lock:
                populate(self.build, modules=(module,))
        finally:
            with self.lock:
                self.running -= 1


@pytest.fixture
def analyzer(repository: Path, monkeypatch) -> RecordingAnalyzer:
    """Replace Lake's preparation and doc-gen's analysis with a recorder."""
    recorder = RecordingAnalyzer(repository)
    monkeypatch.setattr(documentation, "prepare_analysis", lambda root, lake: recorder)
    return recorder


def new_modules(analyzer: RecordingAnalyzer) -> list[str]:
    """Return and forget the modules analyzed since the previous call."""
    modules, analyzer.modules = sorted(analyzer.modules), []
    return modules


def write_fake_lake(tmp_path: Path, calls: Path) -> Path:
    """Write a Lake stand-in that records calls and provides a fake doc-gen."""
    tools = tmp_path / "tools"
    tools.mkdir()
    analyzer = tools / "doc-gen4"
    analyzer.write_text("#!/bin/sh\n")
    analyzer.chmod(0o755)
    lake = tmp_path / "lake"
    lake.write_text(
        f"#!{sys.executable}\n"
        "import json, os, sys\n"
        f"with open({str(calls)!r}, 'a') as stream:\n"
        "    stream.write(json.dumps([os.getcwd(), sys.argv[1:]]) + '\\n')\n"
        "if sys.argv[1] == 'query':\n"
        "    print('https://example.com/pool/blob/commit')\n"
        "if sys.argv[1] == 'env':\n"
        f"    os.environ['PATH'] = {str(tools)!r} + os.pathsep + os.environ['PATH']\n"
        "    os.environ['LEAN_PATH'] = 'compiled'\n"
        "    os.execvp(sys.argv[2], sys.argv[2:])\n"
    )
    lake.chmod(0o755)
    return lake


def test_import_order_ignores_comments_and_strings(repository: Path) -> None:
    """Read as imports, the commented and quoted self-imports would be a cycle."""
    modules = documentation.ordered_modules(repository)
    assert modules == ["LeanPool", "LeanPool.A", "LeanPool.Z"]
    assert documentation.external_modules(repository) == ["Init", "Lake", "Lean", "Std"]


def test_projects_are_listed_one_after_another(repository: Path) -> None:
    """A pool-wide depth order would finish every large project only at the end."""
    for project, depth in (("Deep", 3), ("Wide", 2)):
        (repository / "LeanPool" / project).mkdir()
        for level in range(depth):
            imported = f"import LeanPool.{project}.M{level - 1}\n" if level else ""
            (repository / "LeanPool" / project / f"M{level}.lean").write_text(
                f"module\n{imported}"
            )
    modules = documentation.ordered_modules(repository, {"Deep", "Wide"})
    assert modules == [
        "LeanPool.Deep.M0",
        "LeanPool.Deep.M1",
        "LeanPool.Deep.M2",
        "LeanPool.Wide.M0",
        "LeanPool.Wide.M1",
    ]


def test_cli_default_bounds_simultaneous_analyzers(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """A cold pool must finish without ever exceeding the fixed analyzer count."""
    for number in range(40):
        (repository / "LeanPool" / f"Independent{number}.lean").write_text("module\n")
    monkeypatch.setattr(
        sys, "argv", ["documentation", "batch", "--repo", str(repository)]
    )
    documentation.main()
    documentation.require_complete(repository)
    assert len(analyzer.modules) == len(set(analyzer.modules)) == 43
    assert 1 < analyzer.peak <= documentation.ANALYZERS


def test_failed_analyzer_starts_no_further_work_and_fails_the_stage(
    repository: Path, monkeypatch
) -> None:
    """An analysis error must surface instead of being recorded as progress."""
    for number in range(20):
        (repository / "LeanPool" / f"Independent{number}.lean").write_text("module\n")
    recorder = RecordingAnalyzer(repository, fail="LeanPool.Independent3")
    monkeypatch.setattr(documentation, "prepare_analysis", lambda root, lake: recorder)
    with pytest.raises(subprocess.CalledProcessError):
        documentation.build_batches(repository, "lake", 60, 128, workers=1)
    assert recorder.modules.index("LeanPool.Independent3") == len(recorder.modules) - 1
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)


def test_failed_reanalysis_rejects_reverted_completion(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """Committed replacement rows cannot retain the previous completion certificate."""
    paths = [repository / "LeanPool" / f"{name}.lean" for name in ("A", "Z")]
    original = [path.read_text() for path in paths]
    assert documentation.build_batches(repository, "lake", 60, 8, workers=1)
    for path, text in zip(paths, original, strict=True):
        path.write_text(text + "-- changed documentation\n")
    analyze = analyzer.analyze

    def replace(module: str) -> None:
        analyze(module)
        populate(analyzer.build, value="changed")

    monkeypatch.setattr(analyzer, "analyze", replace)
    analyzer.fail = "LeanPool.Z"
    with pytest.raises(subprocess.CalledProcessError):
        documentation.build_batches(repository, "lake", 60, 8, workers=1)
    with sqlite3.connect(analyzer.build / "api-docs.db") as connection:
        assert connection.execute("SELECT value FROM contents").fetchone() == (
            "changed",
        )
    for path, text in zip(paths, original, strict=True):
        path.write_text(text)
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    analyzer.fail = None
    analyzer.modules.clear()
    assert documentation.build_batches(repository, "lake", 60, 8, workers=1)
    assert set(analyzer.modules) == {"LeanPool.A", "LeanPool.Z"}
    documentation.require_complete(repository)


def test_failed_preparation_invalidates_completion(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """A prerequisite can commit database rows before preparation fails."""
    assert documentation.build_batches(repository, "lake", 60, 8, workers=1)

    def fail_after_write(root: Path, lake: str) -> None:
        populate(analyzer.build, value="changed by prerequisite")
        raise RuntimeError("prerequisite failed after writing")

    monkeypatch.setattr(documentation, "prepare_analysis", fail_after_write)
    with pytest.raises(RuntimeError, match="prerequisite failed"):
        documentation.build_batches(repository, "lake", 60, 8, workers=1)
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)


def test_failed_pruning_rejects_restored_modules(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """Restoring a removed source must not certify its pruned database rows."""
    assert documentation.build_batches(repository, "lake", 60, 8, workers=1)
    path = repository / "LeanPool" / "A.lean"
    original = path.read_text()
    path.unlink()

    def fail_after_pruning(root: Path, projects: set[str]) -> list[str]:
        raise RuntimeError("failed after pruning")

    monkeypatch.setattr(documentation, "ordered_modules", fail_after_pruning)
    with pytest.raises(RuntimeError, match="failed after pruning"):
        documentation.build_batches(repository, "lake", 60, 8, workers=1)
    with sqlite3.connect(analyzer.build / "api-docs.db") as connection:
        assert connection.execute(
            "SELECT COUNT(*) FROM modules WHERE name = 'LeanPool.A'"
        ).fetchone() == (0,)
    path.write_text(original)
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)


def test_legacy_checkpoint_reanalyzes_possibly_replaced_rows(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """A pre-fix completion certificate may already disagree with its database."""
    current_version = documentation.STATE_VERSION
    monkeypatch.setattr(documentation, "STATE_VERSION", 2)
    assert documentation.build_batches(repository, "lake", 60, 8, workers=1)
    populate(analyzer.build, value="legacy replacement after failure")
    monkeypatch.setattr(documentation, "STATE_VERSION", current_version)
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    analyzer.modules.clear()
    assert documentation.build_batches(repository, "lake", 60, 8, workers=1)
    assert set(analyzer.modules) == {"LeanPool", "LeanPool.A", "LeanPool.Z"}
    documentation.require_complete(repository)


def test_analyzer_runs_doc_gen_like_its_lake_facet(tmp_path: Path, caplog) -> None:
    """The direct command must match the facet's arguments and environment."""
    build = tmp_path / "docbuild" / ".lake" / "build"
    build.mkdir(parents=True)
    script = tmp_path / "doc-gen4"
    script.write_text(
        f"#!{sys.executable}\n"
        "import json, os, sys\n"
        "print('WARNING: noted')\n"
        "json.dump([sys.argv[1:], os.getcwd(), os.environ['LEAN_PATH']], "
        "open('seen.json', 'w'))\n"
        "sys.exit(int(os.environ['STATUS']))\n"
    )
    script.chmod(0o755)
    environment = {"LEAN_PATH": "compiled", "STATUS": "0"}
    analyzer = documentation.Analyzer(
        str(script), environment, build, "https://example.com/pool/blob/commit"
    )
    with caplog.at_level(logging.INFO):
        analyzer.analyze("LeanPool.Project.Module")
    assert json.loads((tmp_path / "docbuild" / "seen.json").read_text()) == [
        [
            "single",
            "--build",
            str(build),
            "LeanPool.Project.Module",
            "api-docs.db",
            "https://example.com/pool/blob/commit/LeanPool/Project/Module.lean",
        ],
        str(tmp_path / "docbuild"),
        "compiled",
    ]
    assert "LeanPool.Project.Module: WARNING: noted" in caplog.text
    environment["STATUS"] = "3"
    with pytest.raises(subprocess.CalledProcessError):
        analyzer.analyze("LeanPool.Project.Module")


def test_stuck_analyzer_is_stopped_and_named(tmp_path: Path, monkeypatch) -> None:
    """A hang must fail with its module instead of exhausting the whole job."""
    build = tmp_path / "docbuild" / ".lake" / "build"
    build.mkdir(parents=True)
    script = tmp_path / "doc-gen4"
    script.write_text(f"#!{sys.executable}\nimport time\ntime.sleep(60)\n")
    script.chmod(0o755)
    monkeypatch.setattr(documentation, "ANALYSIS_SECONDS", 0.2)
    analyzer = documentation.Analyzer(str(script), {}, build, "https://example.com")
    with pytest.raises(subprocess.TimeoutExpired, match="LeanPool.Stuck"):
        analyzer.analyze("LeanPool.Stuck")


def test_lake_prepares_every_input_before_direct_analysis(tmp_path: Path) -> None:
    """Lake must still compile the pool and doc-gen's prerequisites first."""
    (tmp_path / "docbuild").mkdir()
    calls = tmp_path / "calls.jsonl"
    lake = write_fake_lake(tmp_path, calls)
    analyzer = documentation.prepare_analysis(tmp_path, str(lake))
    recorded = [json.loads(line) for line in calls.read_text().splitlines()]
    docbuild = str(tmp_path / "docbuild")
    assert [(directory, command[:2]) for directory, command in recorded] == [
        (str(tmp_path), ["build", "LeanPool"]),
        (docbuild, ["build", "doc-gen4"]),
        (docbuild, ["query", documentation.SOURCE_TARGET]),
        (docbuild, ["env", sys.executable]),
    ]
    assert recorded[1][1][1:] == list(documentation.PREREQUISITES)
    assert analyzer.executable == str(tmp_path / "tools" / "doc-gen4")
    assert analyzer.environment["LEAN_PATH"] == "compiled"
    assert analyzer.build == tmp_path / "docbuild" / ".lake" / "build"
    assert analyzer.sources == "https://example.com/pool/blob/commit"


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


def test_resume_reanalyzes_only_changed_projects(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """An edit sends its project and importers back; shared inputs reset all."""
    everything = ["LeanPool", "LeanPool.A", "LeanPool.Z"]
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert new_modules(analyzer) == everything
    documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert new_modules(analyzer) == []
    (repository / "LeanPool" / "Z.lean").write_text("module\n-- changed\n")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 2)
    assert new_modules(analyzer) == ["LeanPool.A", "LeanPool.Z"]
    documentation.require_complete(repository)
    monkeypatch.setenv("DOCGEN_DEPS_DOCS_URL", "https://example.com/new-docs")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(analyzer) == everything


def test_modules_compiled_by_preparation_are_recorded_as_analyzed(
    repository: Path, monkeypatch
) -> None:
    """Lake may compile stale modules first; fingerprint what was then analyzed."""
    recorder = RecordingAnalyzer(repository)

    def prepare(root: Path, lake: str) -> RecordingAnalyzer:
        compile_modules(repository)
        return recorder

    monkeypatch.setattr(documentation, "prepare_analysis", prepare)
    assert documentation.build_batches(repository, "lake", 60, 3)
    documentation.require_complete(repository)
    assert len(new_modules(recorder)) == 3
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(recorder) == []


def test_option_edit_reuses_projects_with_unchanged_compiled_modules(
    repository: Path, analyzer: RecordingAnalyzer
) -> None:
    """Pool options reach pages only through compiled modules, so hash those instead."""
    compile_modules(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    new_modules(analyzer)
    (repository / "lakefile.toml").write_text("changed options\n")
    documentation.require_complete(repository)
    compile_modules(repository, "1", "LeanPool.A")
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(analyzer) == ["LeanPool.A"]


@pytest.mark.parametrize("contents", [None, "broken", '{"name": "LeanPool.Z"}'])
def test_missing_inventory_hashes_the_whole_pool(
    repository: Path, analyzer: RecordingAnalyzer, contents
) -> None:
    """Without Lake's import inventory, any pool edit re-analyzes the project."""
    path = repository / documentation.IR / "LeanPool/A.setup.json"
    if contents is None:
        path.unlink()
    else:
        path.write_text(contents)
    assert documentation.build_batches(repository, "lake", 60, 3)
    new_modules(analyzer)
    (repository / "LeanPool.lean").write_text("module\n-- changed\n")
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(analyzer) == ["LeanPool", "LeanPool.A"]


def test_option_edit_without_compiled_hashes_reanalyzes_everything(
    repository: Path, analyzer: RecordingAnalyzer
) -> None:
    """Missing Lake hashes conservatively tie every project to the pool options."""
    assert documentation.build_batches(repository, "lake", 60, 3)
    new_modules(analyzer)
    (repository / "lakefile.toml").write_text("changed options\n")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert len(new_modules(analyzer)) == 3


def test_deleted_modules_and_lake_markers_leave_the_checkpoint(
    repository: Path, analyzer: RecordingAnalyzer
) -> None:
    """A removed module cannot keep a page, nor a marker vouch for replaced records."""
    assert documentation.build_batches(repository, "lake", 60, 3)
    build = repository / "docbuild" / ".lake" / "build"
    populate(build, modules=("Mathlib.Logic.Basic",))
    (build / "doc-data").mkdir()
    for name in ("LeanPool.Z.doc", "LeanPool.Z.doc.trace", "references.json"):
        (build / "doc-data" / name).write_text("lake")
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
    assert [path.name for path in (build / "doc-data").iterdir()] == ["references.json"]
    documentation.require_complete(repository)


def test_deadline_keeps_analyzed_modules_and_resumes_the_rest(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """Running out of time inside a large project must not repeat its finished part."""
    (repository / "LeanPool" / "Large").mkdir()
    for number in range(6):
        (repository / "LeanPool" / "Large" / f"M{number}.lean").write_text("module\n")
    clock = [0.0]
    monkeypatch.setattr(documentation.time, "monotonic", lambda: clock[0])
    analyze = analyzer.analyze

    def expire_after_five(module: str) -> None:
        analyze(module)
        if len(analyzer.modules) == 5:
            clock[0] = 61

    monkeypatch.setattr(analyzer, "analyze", expire_after_five)
    assert not documentation.build_batches(repository, "lake", 60, 2, workers=1)
    first = new_modules(analyzer)
    assert len(first) == 5
    build = repository / "docbuild" / ".lake" / "build"
    state = json.loads((build / documentation.STATE).read_text())
    assert sorted(state["projects"]) == ["", "A"]
    assert state["partial"]["Large"]["modules"] == [
        module for module in first if module.startswith("LeanPool.Large.")
    ]
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    monkeypatch.setattr(analyzer, "analyze", analyze)
    assert documentation.build_batches(repository, "lake", 60, 2, workers=1)
    assert set(new_modules(analyzer)).isdisjoint(first)
    assert len(analyzer.modules) == 0
    documentation.require_complete(repository)
    state = json.loads((build / documentation.STATE).read_text())
    assert state["partial"] == {}


def test_stage_without_any_analysis_reports_no_progress(
    repository: Path, analyzer: RecordingAnalyzer, monkeypatch
) -> None:
    """A stage that cannot advance must fail rather than repeat silently."""
    clock = iter([0.0])
    monkeypatch.setattr(documentation.time, "monotonic", lambda: next(clock, 61.0))
    with pytest.raises(RuntimeError, match="no module was analyzed"):
        documentation.build_batches(repository, "lake", 60, 2)
    assert analyzer.modules == []


def test_changed_project_discards_its_partial_progress(
    repository: Path, analyzer: RecordingAnalyzer
) -> None:
    """Modules analyzed before an edit to their project must be analyzed again."""
    (repository / "LeanPool" / "Large").mkdir()
    for number in range(3):
        (repository / "LeanPool" / "Large" / f"M{number}.lean").write_text("module\n")
    build = repository / "docbuild" / ".lake" / "build"
    fingerprints = documentation.project_fingerprints(repository)
    documentation.write_progress(
        build,
        documentation.input_identity(repository),
        {},
        {"Large": {"LeanPool.Large.M0", "LeanPool.Large.M1"}},
        fingerprints,
    )
    (repository / "LeanPool" / "Large" / "M2.lean").write_text("module\n-- changed\n")
    assert documentation.build_batches(repository, "lake", 60, 128)
    assert len(new_modules(analyzer)) == 6
    documentation.require_complete(repository)


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


def test_stage_job_outlasts_its_analysis_allowance() -> None:
    """A job stopped before its allowance ends would save no checkpoint at all."""
    workflow = Path(__file__).resolve().parents[2] / ".github/workflows/docs-build.yml"
    job = yaml.safe_load(workflow.read_text())["jobs"]["build"]
    command = next(step for step in job["steps"] if step.get("id") == "analysis")
    allowance = int(command["run"].split("--seconds ")[1].split()[0])
    setup = 3600
    assert (
        allowance + documentation.ANALYSIS_SECONDS + setup
        <= job["timeout-minutes"] * 60
    )


@pytest.mark.parametrize("artifact", ["olean.server", "olean.private"])
def test_companion_only_changes_invalidate_completion_and_reanalyze(
    repository: Path, analyzer: RecordingAnalyzer, artifact: str
) -> None:
    """Unchanged public oleans cannot conceal new documentation metadata."""
    compile_modules(repository)
    compile_modules(repository, "old", "LeanPool.A", artifact=artifact)
    assert documentation.build_batches(repository, "lake", 60, 3)
    documentation.require_complete(repository)
    new_modules(analyzer)
    (repository / "lakefile.toml").write_text("changed documentation options\n")
    compile_modules(repository, "new", "LeanPool.A", artifact=artifact)
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(analyzer) == ["LeanPool.A"]
    documentation.require_complete(repository)


@pytest.mark.parametrize("artifact", ["olean.server", "olean.private"])
def test_companion_presence_and_absence_invalidate_completed_projects(
    repository: Path, analyzer: RecordingAnalyzer, artifact: str
) -> None:
    """Legacy modules may omit companions, but their later appearance matters."""
    compile_modules(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    documentation.require_complete(repository)
    new_modules(analyzer)
    compile_modules(repository, "new", "LeanPool.A", artifact=artifact)
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    path = repository / documentation.COMPILED / f"LeanPool/A.{artifact}"
    path.unlink()  # A leftover hash must not stand in for an absent artifact.
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(analyzer) == ["LeanPool.A"] * 2
    documentation.require_complete(repository)


@pytest.mark.parametrize("artifact", ["olean", "olean.server", "olean.private"])
def test_missing_cached_hash_still_tracks_actual_artifact_content(
    repository: Path, analyzer: RecordingAnalyzer, artifact: str
) -> None:
    """Hash actual output when Lake's sidecar is absent, without guessing validity."""
    compile_modules(repository)
    compile_modules(
        repository, "old", "LeanPool.A", artifact=artifact, cache_hash=False
    )
    assert documentation.build_batches(repository, "lake", 60, 3)
    new_modules(analyzer)
    compile_modules(
        repository, "new", "LeanPool.A", artifact=artifact, cache_hash=False
    )
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(analyzer) == ["LeanPool.A"]
    documentation.require_complete(repository)


def test_missing_public_artifact_keeps_conservative_configuration_identity(
    repository: Path, analyzer: RecordingAnalyzer
) -> None:
    """An old hash alone is not evidence of a current compiled public module."""
    compile_modules(repository)
    (repository / documentation.COMPILED / "LeanPool/A.olean").unlink()
    assert documentation.build_batches(repository, "lake", 60, 3)
    new_modules(analyzer)
    (repository / "lakefile.toml").write_text("changed options\n")
    with pytest.raises(ValueError, match="incomplete"):
        documentation.require_complete(repository)
    assert documentation.build_batches(repository, "lake", 60, 3)
    assert new_modules(analyzer) == ["LeanPool.A"]
