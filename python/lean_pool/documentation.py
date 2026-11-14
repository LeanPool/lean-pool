"""Build resumable local API documentation outside pull-request CI.

Progress is recorded per project: a project whose sources and compiled modules
are unchanged is never handed to Lake again, so routine merges, option edits and
helper changes do not restart the whole pool. Only successful batches record
progress. A timed-out or failed subprocess is stopped together with its children
before its database and Lake markers are rolled back to the preceding consistent
checkpoint. Lake still checks its own traces for every project it is given.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import re
import shutil
import signal
import sqlite3
import subprocess
import tempfile
import time
from contextlib import contextmanager
from graphlib import TopologicalSorter
from pathlib import Path

from lean_pool.exposition.source_text import code_view
from lean_pool.indexes import structure_errors

LOGGER = logging.getLogger(__name__)
IMPORTS = re.compile(
    r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]+)"
)
STATE = "documentation-progress.json"
# Bump when stored analysis must be discarded, e.g. a changed database contract.
STATE_VERSION = 2
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


def read_progress(build: Path, identity: str) -> dict[str, str]:
    """Return completed project fingerprints saved under the same shared inputs."""
    path = build / STATE
    state = json.loads(path.read_text()) if path.exists() else {}
    if state.get("identity") != identity:
        return {}
    projects = state.get("projects")
    if not isinstance(projects, dict):
        raise ValueError("invalid documentation checkpoint progress")
    return projects


def ordered_modules(root: Path, projects: set[str] | None = None) -> list[str]:
    """Visit dependencies first so one target cannot hide an unbounded cold closure.

    Restricting to `projects` skips parsing the rest. Lake still fetches the
    analysis of any module imported from another project; that project's own
    record says whether its pages are already current.
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
    return list(TopologicalSorter(graph).static_order())


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
    """Delete analysis of local modules that no longer exist, with their markers.

    doc-gen cascades every table from `modules`. Removing the marker too keeps a
    module that later reappears unchanged from being skipped by Lake's trace.
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
    for name in stale:
        for marker in (build / "doc-data").glob(f"{name}.doc*"):
            marker.unlink()
    return stale


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


@contextmanager
def batch_checkpoint(build: Path):
    """Restore the last complete database/marker pair if a batch fails or times out."""
    build.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="lean-pool-docs-") as directory:
        saved = Path(directory)
        database = build / "api-docs.db"
        if database.exists():
            validate_database(build)
            shutil.copy2(database, saved / database.name)
        markers = build / "doc-data"
        if markers.exists():
            shutil.copytree(markers, saved / markers.name)
        try:
            yield
        except BaseException:
            for suffix in ("", "-wal", "-shm", "-journal"):
                (build / f"api-docs.db{suffix}").unlink(missing_ok=True)
            shutil.rmtree(markers, ignore_errors=True)
            if (saved / database.name).exists():
                shutil.copy2(saved / database.name, database)
            if (saved / markers.name).exists():
                shutil.copytree(saved / markers.name, markers)
            raise


def stop_build(process: subprocess.Popen) -> None:
    """Stop descendants even when their failed parent has already exited."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # A parent can exit before a child that still holds the SQLite database.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def run_build(command: list[str], directory: Path, timeout: float) -> None:
    """Bound a native build and reap its entire process group before rollback."""
    process = subprocess.Popen(command, cwd=directory, start_new_session=True)
    try:
        status = process.wait(timeout=timeout)
    except BaseException:
        stop_build(process)
        raise
    if status:
        stop_build(process)
        raise subprocess.CalledProcessError(status, command)


def build_batches(root: Path, lake: str, seconds: float, batch_size: int) -> bool:
    """Analyze changed projects in verified batches until done or out of time."""
    if seconds <= 0 or batch_size <= 0:
        raise ValueError("batch size and time allowance must be positive")
    build = root / "docbuild" / ".lake" / "build"
    identity = input_identity(root)
    fingerprints = project_fingerprints(root)
    done = {
        project: value
        for project, value in read_progress(build, identity).items()
        if fingerprints.get(project) == value
    }
    with batch_checkpoint(build):
        if stale := prune_modules(build, set(module_sources(root))):
            validate_database(build)
            LOGGER.info("Removed %s deleted modules", len(stale))
    pending = ordered_modules(root, set(fingerprints) - set(done))
    remaining: dict[str, int] = {}
    for module in pending:
        remaining[project_of(module)] = remaining.get(project_of(module), 0) + 1
    LOGGER.info(
        "Documentation analysis: %s/%s projects reused, %s modules to check",
        len(done),
        len(fingerprints),
        len(pending),
    )
    write_progress(build, identity, done)
    deadline = time.monotonic() + seconds
    position = 0
    while position < len(pending) and time.monotonic() < deadline:
        batch = pending[position : position + batch_size]
        command = [lake, "build", *(f"+{name}:docInfo" for name in batch)]
        try:
            with batch_checkpoint(build):
                run_build(
                    command, root / "docbuild", max(1, deadline - time.monotonic())
                )
                validate_database(build)
        except subprocess.TimeoutExpired:
            if position == 0:
                raise RuntimeError(
                    "no batch completed within the time allowance"
                ) from None
            break
        position += len(batch)
        finished = set()
        for module in batch:
            remaining[project_of(module)] -= 1
            if not remaining[project_of(module)]:
                finished.add(project_of(module))
        # Lake may have compiled modules during the batch, so fingerprint the
        # finished projects as analyzed rather than as they were at the start.
        if finished:
            done.update(project_fingerprints(root, finished))
        write_progress(build, identity, done)
        LOGGER.info("Documentation analysis: %s/%s modules", position, len(pending))
    return done == project_fingerprints(root)


def write_progress(build: Path, identity: str, done: dict[str, str]) -> None:
    """Record completed projects, dropping those that no longer exist."""
    build.mkdir(parents=True, exist_ok=True)
    state = {"identity": identity, "projects": dict(sorted(done.items()))}
    (build / STATE).write_text(json.dumps(state) + "\n")


def require_complete(root: Path) -> None:
    """Refuse to render or publish an incomplete or different source snapshot."""
    build = root / "docbuild" / ".lake" / "build"
    if read_progress(build, input_identity(root)) != project_fingerprints(root):
        raise ValueError("documentation analysis is incomplete for this snapshot")
    validate_database(build)


def render(root: Path, lake: str) -> None:
    """Render fresh local pages from the complete analysis checkpoint."""
    require_complete(root)
    build = root / "docbuild" / ".lake" / "build"
    shutil.rmtree(build / "doc" / "LeanPool", ignore_errors=True)
    # Loading one import-all Lean environment would combine the independent
    # projects' memory requirements. The database already holds every local
    # module; only external names need an environment before rendering it.
    dependencies = compiled_dependencies(root)
    if dependencies:
        subprocess.run(
            [lake, "build", *dependencies], cwd=root / "docbuild", check=True
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


def validate_site(root: Path) -> None:
    """Require every local module page and reject accidentally rendered dependencies."""
    site = root / "docbuild" / ".lake" / "build" / "doc"
    required = ["index.html", "declarations/declaration-data.bmp"]
    required += [name.replace(".", "/") + ".html" for name in module_sources(root)]
    missing = [
        name
        for name in required
        if not (site / name).is_file() or (site / name).stat().st_size == 0
    ]
    if missing:
        raise ValueError(f"missing documentation pages: {missing[:10]}")
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
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO)
    root = arguments.repo.resolve()
    if arguments.command == "prepare":
        prepare(root)
    elif arguments.command == "batch":
        complete = build_batches(
            root, arguments.lake, arguments.seconds, arguments.batch_size
        )
        if output := os.environ.get("GITHUB_OUTPUT"):
            with Path(output).open("a") as stream:
                stream.write(f"complete={str(complete).lower()}\n")
    elif arguments.command == "render":
        render(root, arguments.lake)
    else:
        require_complete(root)
        validate_site(root)


if __name__ == "__main__":
    main()
