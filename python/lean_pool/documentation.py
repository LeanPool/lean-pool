"""Build resumable local API documentation outside pull-request CI.

Lake compiles the pool and doc-gen's prerequisites; the analysis of each module
then runs as its own doc-gen process, a fixed number at a time. doc-gen replaces
a module's records in one transaction, so the database only ever holds whole
modules and needs no rollback. Progress is recorded per project, and per module
inside an unfinished project: a project whose sources and compiled modules are
unchanged is never analyzed again, so routine merges, option edits and helper
changes do not restart the whole pool.

The site holds every module of every project doc-gen can analyze. A project
with a module it cannot analyze within the machine's memory or the time allowed
is left out whole, listed in the site's `undocumented.json` and in the run's
warnings, and analyzed again once its sources change. A few projects import
another one; their pages are still rendered when that one is left out, with
nothing to link to for its declarations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from graphlib import TopologicalSorter
from pathlib import Path

from lean_pool.build_time_limits import (
    MEMORY_FLOOR_BYTES,
    free_memory,
    process_memory,
)
from lean_pool.exposition.source_text import code_view
from lean_pool.indexes import structure_errors

LOGGER = logging.getLogger(__name__)
IMPORTS = re.compile(
    r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]+)"
)
STATE = "documentation-progress.json"
# Bump when stored analysis must be discarded, e.g. a changed database contract.
STATE_VERSION = 3
# One analyzer per hosted-runner core. Lake could not hold this bound: jobs
# resuming from dependency waits exceeded its worker limit and exhausted memory.
ANALYZERS = 4
# Ordinary modules take seconds. A stuck analyzer must fail by name instead of
# silently consuming the job's remaining time.
ANALYSIS_SECONDS = 1800
# doc-gen can allocate without end on a single module: on 2026-11-21 it gained
# 55 MiB a second on LeanPool.FastDynamo.Fourier.PeriodicH2 and passed 27 GiB.
# A 16 GB runner then dies without a message and without saving the stage. So
# when the machine is about to run out, the analyzer holding the most is stopped
# and named. No fixed size per analyzer: a module that fits today keeps fitting.
MEMORY_POLL_SECONDS = 1.0
# A project is left out of a publication when doc-gen cannot analyze one of its
# modules: stopped while holding at least this much, or still running after
# ANALYSIS_SECONDS. That is a property of the project's declarations, which its
# authors can change, and must not keep every other project's pages from being
# published. An analyzer stopped while holding less was a victim of a shortage
# it did not cause, and fails the stage as before.
UNDOCUMENTED_MEMORY_BYTES = 4 * 1024**3
# More projects than this in one publication means the fault is ours (doc-gen,
# the runner), so the stage fails instead of publishing a hollow site.
MAX_UNDOCUMENTED_PROJECTS = 3
# What doc-gen's `docInfo` facet builds before it analyzes a local module.
PREREQUISITES = ("doc-gen4", "doc-gen4/bibPrepass", "doc-gen4/coreDocs")
SOURCE_TARGET = "lean-pool/LeanPool:srcUri"
ENVIRONMENT = "import json, os; print(json.dumps(dict(os.environ)))"
TOOLCHAIN_ROOTS = frozenset({"Init", "Std", "Lean", "Lake"})
COMPILED = Path(".lake/build/lib/lean")
IR = Path(".lake/build/ir")
LINK_POLICY = (
    "DOCGEN_LOCAL_MODULE_ROOTS",
    "DOCGEN_DEPS_DOCS_URL",
    "DOCGEN_DEPS_DOCS_URLS",
)


def module_sources(root: Path) -> dict[str, Path]:
    """Discover every local module, including the empty library root."""
    paths = [root / "LeanPool.lean", *sorted((root / "LeanPool").rglob("*.lean"))]
    return {
        ".".join(path.relative_to(root).with_suffix("").parts): path for path in paths
    }


def _digest_files(digest, root: Path, paths: list[Path]) -> None:
    for path in sorted(paths):
        digest.update(str(path.relative_to(root)).encode())
        digest.update(b"\0" + path.read_bytes() + b"\0")


def input_identity(root: Path) -> str:
    """Name the toolchain, dependency, doc-gen and link-policy inputs of every page.

    The pool's own `lakefile.toml` is left out: its options reach the analysis
    only through compiled modules, which `project_fingerprints` hashes directly.
    """
    digest = hashlib.sha256(f"version={STATE_VERSION}\0".encode())
    _digest_files(
        digest,
        root,
        [
            root / "lean-toolchain",
            root / "lake-manifest.json",
            *(
                root / "docbuild" / name
                for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
            ),
        ],
    )
    for name in LINK_POLICY:
        digest.update(name.encode() + b"=" + os.environ.get(name, "").encode() + b"\0")
    return digest.hexdigest()


def project_of(module: str) -> str:
    """Group `LeanPool.<Project>...` modules; the empty library root is its own."""
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else ""


def local_closure(root: Path, project: str, modules: set[str]) -> set[str] | None:
    """Read the project's local transitive imports from Lake's setup files.

    The entry module and `Imports` aggregate together import every project
    source, so their inventories cover modules borrowed from other projects.
    Return None unless they cover all of the project's own modules.
    """
    entry = "LeanPool" + (f".{project}" if project else "")
    own = {module for module in modules if project_of(module) == project}
    closure = own & {entry, f"{entry}.Imports"}
    for module in sorted(closure):
        setup = root / IR / (module.replace(".", "/") + ".setup.json")
        try:
            inventory = json.loads(setup.read_text())
            if inventory["name"] != module or not isinstance(
                inventory["importArts"], dict
            ):
                return None
        except (OSError, ValueError, KeyError, TypeError):
            return None
        closure |= modules & set(inventory["importArts"])
    return closure if own <= closure else None


def compiled_module_hashes(root: Path, source: Path) -> dict[str, str | None]:
    """Identify each consumed module artifact, including absent legacy companions.

    Lake's cached content hash is used when available. Otherwise stream the
    artifact itself, so a missing hash never hides a changed companion.
    """
    identities = {}
    for suffix in ("olean", "olean.server", "olean.private"):
        artifact = root / COMPILED / source.relative_to(root).with_suffix(f".{suffix}")
        if not artifact.is_file():
            identities[suffix] = None
            continue
        cached = Path(f"{artifact}.hash")
        identity = cached if cached.is_file() and cached.stat().st_size else artifact
        with identity.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        kind = "cached" if identity == cached else "artifact"
        identities[suffix] = f"{kind}:{digest}"
    return identities


def project_fingerprints(
    root: Path, projects: set[str] | None = None
) -> dict[str, str]:
    """Hash the sources and compiled modules each project's pages depend on.

    That is the project's modules plus every pool module they import, from other
    projects too. Without Lake's import inventory the whole pool is included.
    Missing public artifacts retain the pool configuration as a fallback; present
    artifacts use cached or directly computed content hashes. Only the closures
    of `projects` (default: all) are read.
    """
    sources = module_sources(root)
    modules = set(sources)
    configuration = hashlib.sha256((root / "lakefile.toml").read_bytes()).hexdigest()
    digests: dict[str, tuple[str, dict[str, str | None]]] = {}

    def digest(module: str) -> tuple[str, dict[str, str | None]]:
        if module not in digests:
            path = sources[module]
            digests[module] = (
                hashlib.sha256(path.read_bytes()).hexdigest(),
                compiled_module_hashes(root, path),
            )
        return digests[module]

    fingerprints = {}
    for project in sorted(projects or {project_of(module) for module in modules}):
        closure = local_closure(root, project, modules) or modules
        entries = {module: digest(module) for module in sorted(closure)}
        if any(compiled["olean"] is None for _, compiled in entries.values()):
            entries["lakefile.toml"] = (configuration, None)
        encoded = json.dumps(entries, sort_keys=True).encode()
        fingerprints[project] = hashlib.sha256(encoded).hexdigest()
    return fingerprints


def read_state(build: Path, identity: str) -> dict:
    """Return the checkpoint saved under the same shared inputs, else an empty one."""
    path = build / STATE
    state = json.loads(path.read_text()) if path.exists() else {}
    if state.get("identity") != identity:
        return {}
    keys = ("projects", "partial", "undocumented")
    if not all(isinstance(state.get(key, {}), dict) for key in keys):
        raise ValueError("invalid documentation checkpoint progress")
    return state


def read_progress(build: Path, identity: str) -> dict[str, str]:
    """Return completed project fingerprints saved under the same shared inputs."""
    return read_state(build, identity).get("projects", {})


def restore_progress(
    build: Path,
    identity: str,
    fingerprints: dict[str, str],
    state: dict | None = None,
) -> tuple[dict[str, str], dict[str, set[str]]]:
    """Return unchanged completed projects, and analyzed modules of unfinished ones."""
    state = read_state(build, identity) if state is None else state
    if state.get("identity") != identity:
        return {}, {}
    done = {
        project: value
        for project, value in state.get("projects", {}).items()
        if fingerprints.get(project) == value
    }
    partial = {
        project: set(record["modules"])
        for project, record in state.get("partial", {}).items()
        if fingerprints.get(project) == record["fingerprint"] and project not in done
    }
    return done, partial


def restore_undocumented(
    fingerprints: dict[str, str], state: dict
) -> dict[str, dict[str, str]]:
    """Return the projects left out earlier whose sources and modules are unchanged.

    A changed project is analyzed again, so repairing its declarations is all it
    takes to bring its pages back.
    """
    return {
        project: dict(record)
        for project, record in state.get("undocumented", {}).items()
        if fingerprints.get(project) == record.get("fingerprint")
    }


def undocumented_projects(root: Path) -> dict[str, dict[str, str]]:
    """Return the projects this snapshot's checkpoint leaves out, with the reason."""
    build = root / "docbuild" / ".lake" / "build"
    return read_state(build, input_identity(root)).get("undocumented", {})


def ordered_modules(root: Path, projects: set[str] | None = None) -> list[str]:
    """List one project after another, each with its dependencies first.

    Analyses are independent, so the order only decides which work is saved
    first: whole projects finish early instead of all at the very end.
    Restricting to `projects` skips parsing the rest.
    """
    sources = {
        name: path
        for name, path in module_sources(root).items()
        if projects is None or project_of(name) in projects
    }
    graph = {}
    for name, path in sources.items():
        imports = {
            item
            for line in IMPORTS.findall(code_view(path.read_text()))
            for item in line.split()
        }
        graph[name] = sorted(imports & sources.keys())
    return sorted(TopologicalSorter(graph).static_order(), key=project_of)


def prepare(root: Path) -> None:
    """Require complete indexes and identical shared dependency/toolchain pins."""
    errors = structure_errors(root)
    if errors:
        raise ValueError(f"invalid project aggregates: {errors[:3]}")
    if (root / "lean-toolchain").read_bytes() != (
        root / "docbuild" / "lean-toolchain"
    ).read_bytes():
        raise ValueError("documentation toolchain differs from the pool")
    manifests = [
        json.loads((directory / "lake-manifest.json").read_text())
        for directory in (root, root / "docbuild")
    ]
    packages = [
        {item["name"].strip("«»"): item for item in manifest["packages"]}
        for manifest in manifests
    ]
    for name, package in packages[0].items():
        inherited = packages[1].get(name, {})
        if any(package.get(field) != inherited.get(field) for field in ("url", "rev")):
            raise ValueError(f"documentation dependency differs from the pool: {name}")


def external_modules(root: Path) -> list[str]:
    """Collect external links without loading a combined pool environment."""
    sources = module_sources(root)
    imports = set(TOOLCHAIN_ROOTS)
    for path in sources.values():
        imports.update(
            item
            for line in IMPORTS.findall(code_view(path.read_text()))
            for item in line.split()
            if item not in sources
        )
    return sorted(imports)


def compiled_dependencies(root: Path) -> list[str]:
    """Name the external modules whose compiled files Lake must provide.

    The Mathlib cache supplies Mathlib and its dependencies, but nothing supplies
    Tau Ceti outside analysis batches, so rendering must build it explicitly.
    """
    return [
        name
        for name in external_modules(root)
        if name.split(".")[0] not in TOOLCHAIN_ROOTS
    ]


def prune_modules(build: Path, modules: set[str]) -> list[str]:
    """Delete analysis of local modules that no longer exist.

    doc-gen cascades every table from `modules`.
    """
    database = build / "api-docs.db"
    if not database.is_file():
        return []
    with sqlite3.connect(database) as connection:
        connection.execute("PRAGMA foreign_keys = ON")
        stored = [
            name
            for (name,) in connection.execute(
                "SELECT name FROM modules WHERE name = 'LeanPool' "
                "OR name LIKE 'LeanPool.%'"
            )
        ]
        stale = sorted(set(stored) - modules)
        connection.executemany(
            "DELETE FROM modules WHERE name = ?", [(name,) for name in stale]
        )
    connection.close()
    return stale


def clean_checkpoint(build: Path, modules: set[str]) -> None:
    """Drop what the pool no longer has, then check the database before adding to it.

    Lake's `docInfo` markers go too: direct analysis never updates them, and a
    stale one would let a later Lake build skip a module whose records changed.
    """
    for marker in (build / "doc-data").glob("LeanPool*.doc*"):
        marker.unlink()
    if stale := prune_modules(build, modules):
        LOGGER.info("Removed %s deleted modules", len(stale))
    if (build / "api-docs.db").exists():
        validate_database(build)


def validate_database(build: Path) -> None:
    """Check a closed batch's SQLite state before retaining it."""
    database = build / "api-docs.db"
    if not database.is_file() or database.stat().st_size == 0:
        raise ValueError("documentation database is missing or empty")
    with sqlite3.connect(database) as connection:
        checkpoint = connection.execute("PRAGMA wal_checkpoint(TRUNCATE)").fetchone()
        integrity = connection.execute("PRAGMA quick_check").fetchone()
    if checkpoint is None or checkpoint[0] != 0 or integrity != ("ok",):
        raise ValueError(f"invalid documentation checkpoint: {checkpoint}, {integrity}")


class AnalysisMemoryError(RuntimeError):
    """An analyzer was stopped because the machine was running out of memory."""

    def __init__(self, message: str, held: int = 0) -> None:
        """Keep what the stopped analyzer held, in bytes."""
        super().__init__(message)
        self.held = held


# The analyzers running now, by process, so the largest one can be found.
_RUNNING: dict[int, str] = {}
_RUNNING_LOCK = threading.Lock()
# One analyzer at a time reads the free memory, decides and, if it is the one
# to go, has exited before the next one looks. Otherwise a second analyzer
# could act on a reading taken before the first one released its memory.
_STOP_LOCK = threading.Lock()


def _gibibytes(size: int) -> str:
    return f"{size / 2**30:.1f} GiB"


def memory_shortage(pid: int) -> tuple[str, int] | None:
    """Say why analyzer ``pid`` must stop and what it holds, or ``None``.

    Only the analyzer holding the most anonymous memory stops, and only when
    the machine has less than the floor left; the others finish their modules.
    """
    free = free_memory()
    if free is None or free >= MEMORY_FLOOR_BYTES:
        return None
    with _RUNNING_LOCK:
        running = dict(_RUNNING)
    held = {process: process_memory(process) or 0 for process in running}
    if (
        pid not in held
        or max(held, key=lambda process: (held[process], -process)) != pid
    ):
        return None
    others = ", ".join(
        f"{module} {_gibibytes(held[process])}"
        for process, module in sorted(running.items())
        if process != pid
    )
    reason = (
        f"it held {_gibibytes(held[pid])} when the machine had {_gibibytes(free)} left"
        + (f" (other analyzers: {others})" if others else "")
    )
    return reason, held[pid]


@dataclass(frozen=True)
class Analyzer:
    """Run doc-gen's single-module analysis exactly as its Lake facet would."""

    executable: str
    environment: dict[str, str]
    build: Path
    sources: str

    def analyze(self, module: str) -> None:
        """Replace one module's records, which doc-gen commits in one transaction."""
        location = "/".join([self.sources, *module.split(".")]) + ".lean"
        command = [self.executable, "single", "--build", str(self.build)]
        command += [module, "api-docs.db", location]
        started = time.monotonic()
        process = subprocess.Popen(
            command,
            cwd=self.build.parents[1],
            env=self.environment,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        with _RUNNING_LOCK:
            _RUNNING[process.pid] = module
        try:
            while True:
                try:
                    output, _ = process.communicate(timeout=MEMORY_POLL_SECONDS)
                    break
                except subprocess.TimeoutExpired:
                    # A retried `communicate` keeps what it has already read.
                    if time.monotonic() - started >= ANALYSIS_SECONDS:
                        process.kill()
                        process.communicate()
                        raise subprocess.TimeoutExpired(
                            command, ANALYSIS_SECONDS
                        ) from None
                    with _STOP_LOCK:
                        shortage = memory_shortage(process.pid)
                        if shortage:
                            process.kill()
                            process.communicate()
                            with _RUNNING_LOCK:
                                _RUNNING.pop(process.pid, None)
                    if shortage:
                        raise AnalysisMemoryError(
                            f"documentation analysis of {module} was stopped: "
                            f"{shortage[0]}",
                            shortage[1],
                        ) from None
        finally:
            with _RUNNING_LOCK:
                _RUNNING.pop(process.pid, None)
        if output := output.strip():
            LOGGER.info("%s: %s", module, output)
        if process.returncode:
            raise subprocess.CalledProcessError(process.returncode, command)


def compile_pool(root: Path, lake: str) -> None:
    """Let Lake bring every compiled module up to date before it is fingerprinted.

    Analysis and rendering restore the same build cache separately. Both
    compile first, so a module only the analysis stage had to compile cannot
    make rendering see a different snapshot.
    """
    subprocess.run([lake, "build", "LeanPool"], cwd=root, check=True)


def prepare_analysis(root: Path, lake: str) -> Analyzer:
    """Let Lake bring every analysis input up to date, then capture how to analyze.

    Lake still decides whether each compiled module and doc-gen prerequisite is
    current. Only the per-module analysis leaves it, because one Lake process
    per group of targets reloaded the import graph and did not bound memory.
    """
    docbuild = root / "docbuild"
    compile_pool(root, lake)
    subprocess.run([lake, "build", *PREREQUISITES], cwd=docbuild, check=True)
    sources = subprocess.check_output(
        [lake, "query", SOURCE_TARGET], cwd=docbuild, text=True
    ).split()
    environment = json.loads(
        subprocess.check_output(
            [lake, "env", sys.executable, "-c", ENVIRONMENT], cwd=docbuild
        )
    )
    executable = shutil.which("doc-gen4", path=environment.get("PATH"))
    if not executable or not sources:
        raise ValueError("Lake did not provide doc-gen or the pool's source location")
    return Analyzer(executable, environment, docbuild / ".lake" / "build", sources[-1])


def undocumented_reason(error: BaseException) -> str | None:
    """Why this failure leaves the module's project out, or ``None`` if it must fail."""
    if isinstance(error, AnalysisMemoryError):
        return str(error) if error.held >= UNDOCUMENTED_MEMORY_BYTES else None
    if isinstance(error, subprocess.TimeoutExpired):
        return f"its documentation analysis ran for {ANALYSIS_SECONDS} seconds"
    return None


def analyze_modules(
    analyzer: Analyzer,
    modules: list[str],
    workers: int,
    deadline: float,
    undocumented: dict[str, dict[str, str]] | None = None,
) -> list[str]:
    """Analyze with a fixed number of processes and return the modules finished.

    No analysis starts after the deadline or after another one failed. Those
    already running complete first, so no writer outlives this call.

    With ``undocumented`` given, a module that doc-gen cannot analyze (see
    `undocumented_reason`) does not fail the call: its project is recorded
    there with the module and the reason, and no further module of that
    project is started.
    """
    queue = iter(modules)
    lock = threading.Lock()
    finished: list[str] = []
    failures: list[BaseException] = []

    def work() -> None:
        while not failures and time.monotonic() < deadline:
            with lock:
                module = next(queue, None)
            if module is None:
                return
            project = project_of(module)
            if undocumented is not None and project in undocumented:
                continue
            try:
                analyzer.analyze(module)
            except BaseException as error:
                reason = None if undocumented is None else undocumented_reason(error)
                if reason is None:
                    failures.append(error)
                    return
                with lock:
                    undocumented.setdefault(
                        project, {"module": module, "reason": reason}
                    )
                continue
            with lock:
                finished.append(module)

    with ThreadPoolExecutor(max_workers=workers) as pool:
        for _ in range(workers):
            pool.submit(work)
    if failures:
        raise failures[0]
    return finished


def build_batches(
    root: Path, lake: str, seconds: float, batch_size: int, workers: int = ANALYZERS
) -> bool:
    """Analyze changed projects in recorded batches until done or out of time."""
    if seconds <= 0 or batch_size <= 0 or workers <= 0:
        raise ValueError("batch size, workers and time allowance must be positive")
    build = root / "docbuild" / ".lake" / "build"
    # Compilation counts against the allowance, so the stage ends on schedule.
    deadline = time.monotonic() + seconds
    previous = read_state(build, input_identity(root))
    # Prerequisites and analyzers may replace rows before a later failure.
    # Keep the reusable snapshot in memory, never as an on-disk certificate.
    write_progress(build, "", {}, {}, {})
    analyzer = prepare_analysis(root, lake)
    identity = input_identity(root)
    fingerprints = project_fingerprints(root)
    done, partial = restore_progress(build, identity, fingerprints, previous)
    undocumented = restore_undocumented(fingerprints, previous)
    write_progress(build, identity, done, partial, fingerprints, undocumented)
    clean_checkpoint(build, set(module_sources(root)))
    pending = [
        module
        for module in ordered_modules(
            root, set(fingerprints) - set(done) - set(undocumented)
        )
        if module not in partial.get(project_of(module), ())
    ]
    remaining = Counter(map(project_of, pending))
    for project in set(fingerprints) - set(done) - set(remaining) - set(undocumented):
        done[project] = fingerprints[project]
    LOGGER.info(
        "Documentation analysis: %s/%s projects reused, %s modules to analyze",
        len(done),
        len(fingerprints),
        len(pending),
    )
    analyzed = left_out = 0
    for position in range(0, len(pending), batch_size):
        if time.monotonic() >= deadline:
            break
        batch = pending[position : position + batch_size]
        finished = analyze_modules(analyzer, batch, workers, deadline, undocumented)
        for project, record in undocumented.items():
            if "fingerprint" not in record:
                record["fingerprint"] = fingerprints[project]
                partial.pop(project, None)
                left_out += 1
                LOGGER.warning("Leaving out project %s: %s", project, record["reason"])
                print(f"::warning::Leaving out project {project}: {record['reason']}")
        if len(undocumented) > MAX_UNDOCUMENTED_PROJECTS:
            raise RuntimeError(
                f"doc-gen could not analyze {len(undocumented)} projects "
                f"({', '.join(sorted(undocumented))}); a publication leaves out "
                f"at most {MAX_UNDOCUMENTED_PROJECTS}"
            )
        for module in finished:
            project = project_of(module)
            if project in undocumented:
                continue
            partial.setdefault(project, set()).add(module)
            remaining[project] -= 1
            analyzed += 1
            if not remaining[project]:
                done[project] = fingerprints[project]
        write_progress(build, identity, done, partial, fingerprints, undocumented)
        LOGGER.info("Documentation analysis: %s/%s modules", analyzed, len(pending))
    if pending and not analyzed and not left_out:
        raise RuntimeError("no module was analyzed within the time allowance")
    write_progress(build, identity, done, partial, fingerprints, undocumented)
    if analyzed:
        validate_database(build)
    accounted = {
        project: record["fingerprint"] for project, record in undocumented.items()
    }
    return accounted | done == project_fingerprints(root)


def resumable(root: Path) -> bool:
    """Whether a failed stage left a checkpoint that the next run may reuse.

    Progress carries the snapshot's identity only once preparation has passed,
    and then lists nothing but batches that finished. A stage that fails before
    that, or with a damaged database, must not replace an older checkpoint.
    """
    build = root / "docbuild" / ".lake" / "build"
    try:
        if not read_state(build, input_identity(root)):
            return False
        validate_database(build)
    except (OSError, ValueError, sqlite3.Error):
        return False
    return True


def write_progress(
    build: Path,
    identity: str,
    done: dict[str, str],
    partial: dict[str, set[str]],
    fingerprints: dict[str, str],
    undocumented: dict[str, dict[str, str]] | None = None,
) -> None:
    """Record completed projects, partly analyzed ones, and those left out."""
    build.mkdir(parents=True, exist_ok=True)
    state = {
        "identity": identity,
        "projects": dict(sorted(done.items())),
        "partial": {
            project: {"fingerprint": fingerprints[project], "modules": sorted(modules)}
            for project, modules in sorted(partial.items())
            if project not in done
        },
    }
    if left_out := {
        project: record
        for project, record in sorted((undocumented or {}).items())
        if project not in done and "fingerprint" in record
    }:
        state["undocumented"] = left_out
    (build / STATE).write_text(json.dumps(state) + "\n")


def require_complete(root: Path) -> None:
    """Refuse to render or publish an incomplete or different source snapshot."""
    build = root / "docbuild" / ".lake" / "build"
    state = read_state(build, input_identity(root))
    accounted = {
        project: record.get("fingerprint")
        for project, record in state.get("undocumented", {}).items()
    }
    if accounted | state.get("projects", {}) != project_fingerprints(root):
        raise ValueError("documentation analysis is incomplete for this snapshot")
    validate_database(build)


def render(root: Path, lake: str) -> None:
    """Render fresh local pages from the complete analysis checkpoint."""
    compile_pool(root, lake)
    require_complete(root)
    build = root / "docbuild" / ".lake" / "build"
    shutil.rmtree(build / "doc" / "LeanPool", ignore_errors=True)
    # A project left out has some analyzed modules; none of them is published.
    left_out = undocumented_projects(root)
    if left_out:
        prune_modules(
            build,
            {name for name in module_sources(root) if project_of(name) not in left_out},
        )
    # Loading one import-all Lean environment would combine the independent
    # projects' memory requirements. The database already holds every local
    # module; only external names need an environment before rendering it.
    subprocess.run(
        [lake, "build", *PREREQUISITES, *compiled_dependencies(root)],
        cwd=root / "docbuild",
        check=True,
    )
    commands = [
        [
            "externals",
            "--build",
            ".lake/build",
            "--srcDirs",
            "..",
            "api-docs.db",
            *external_modules(root),
        ],
        [
            "fromDb",
            "--build",
            ".lake/build",
            "--manifest",
            ".lake/build/doc-manifest.json",
            ".lake/build/api-docs.db",
        ],
    ]
    for command in commands:
        subprocess.run(
            [lake, "exe", "doc-gen4", *command], cwd=root / "docbuild", check=True
        )
    validate_site(root)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True)
    (build / "doc" / "SOURCE_SHA").write_text(commit)
    report_undocumented(build / "doc", left_out)


def report_undocumented(site: Path, left_out: dict[str, dict[str, str]]) -> None:
    """Publish and announce which projects this site leaves out, and why."""
    report = {
        project: {"module": record["module"], "reason": record["reason"]}
        for project, record in sorted(left_out.items())
    }
    (site / "undocumented.json").write_text(json.dumps(report, indent=2) + "\n")
    lines = [
        f"Project {project} is not in this documentation: {record['reason']}"
        for project, record in report.items()
    ]
    for line in lines:
        print(f"::warning::{line}")
    if lines and (summary := os.environ.get("GITHUB_STEP_SUMMARY")):
        with Path(summary).open("a") as stream:
            stream.write("\n".join(["### Projects left out", "", *lines, ""]))


def validate_site(root: Path) -> None:
    """Require every module page of every documented project, and nothing else.

    A project that was left out must have no page at all, and dependencies must
    not have been rendered by accident.
    """
    site = root / "docbuild" / ".lake" / "build" / "doc"
    left_out = undocumented_projects(root)
    pages = {name: name.replace(".", "/") + ".html" for name in module_sources(root)}
    required = ["index.html", "declarations/declaration-data.bmp"]
    required += [
        page for name, page in pages.items() if project_of(name) not in left_out
    ]
    missing = [
        name
        for name in required
        if not (site / name).is_file() or (site / name).stat().st_size == 0
    ]
    if missing:
        raise ValueError(f"missing documentation pages: {missing[:10]}")
    partial = [
        page
        for name, page in pages.items()
        if project_of(name) in left_out and (site / page).exists()
    ]
    if partial:
        raise ValueError(f"pages of a project that was left out: {partial[:10]}")
    for name in ("Mathlib", "TauCeti", "Init", "Std", "Lean", "Lake"):
        if (site / name).exists() or (site / f"{name}.html").exists():
            raise ValueError(f"unexpected dependency documentation: {name}")


def main() -> None:
    """Expose preparation, bounded analysis and complete-site rendering commands."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("prepare", "batch", "render", "validate"))
    parser.add_argument("--repo", type=Path, default=Path("."))
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--seconds", type=float, default=5400)
    parser.add_argument("--batch-size", type=int, default=128)
    parser.add_argument("--workers", type=int, default=ANALYZERS)
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO)
    root = arguments.repo.resolve()
    if arguments.command == "prepare":
        prepare(root)
    elif arguments.command == "batch":
        output = os.environ.get("GITHUB_OUTPUT")
        try:
            complete = build_batches(
                root,
                arguments.lake,
                arguments.seconds,
                arguments.batch_size,
                arguments.workers,
            )
        except BaseException as error:
            # The stage still fails. Its finished batches are saved when they
            # are valid, so one module cannot cost every later run the hours
            # of analysis that came before it.
            if isinstance(error, AnalysisMemoryError):
                print(f"::error::{error}")
            if output:
                with Path(output).open("a") as stream:
                    stream.write(f"resumable={str(resumable(root)).lower()}\n")
            raise
        if output:
            with Path(output).open("a") as stream:
                stream.write(f"complete={str(complete).lower()}\n")
    elif arguments.command == "render":
        render(root, arguments.lake)
    else:
        require_complete(root)
        validate_site(root)


if __name__ == "__main__":
    main()
