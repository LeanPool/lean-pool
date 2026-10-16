"""Build resumable local API documentation outside pull-request CI.

Only successful batches advance the cursor. A timed-out or failed subprocess
is stopped together with its children before its database and Lake markers are
rolled back to the preceding consistent checkpoint. Lake still checks its own
traces when a new source snapshot invalidates the cursor.
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


def module_sources(root: Path) -> dict[str, Path]:
    """Discover every local module, including the empty library root."""
    paths = [root / "LeanPool.lean", *sorted((root / "LeanPool").rglob("*.lean"))]
    return {
        ".".join(path.relative_to(root).with_suffix("").parts): path for path in paths
    }


def input_identity(root: Path) -> str:
    """Invalidate the cursor on changes to sources, pins, helpers or link policy."""
    digest = hashlib.sha256()
    paths = [
        *module_sources(root).values(),
        *(
            root / name
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
        ),
        *(
            root / "docbuild" / name
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
        ),
        Path(__file__),
        Path(__file__).with_name("indexes.py"),
        Path(__file__).parent / "exposition" / "source_text.py",
    ]
    for path in paths:
        name = path.relative_to(root) if path.is_relative_to(root) else Path(path.name)
        digest.update(str(name).encode())
        digest.update(b"\0" + path.read_bytes() + b"\0")
    for name in (
        "DOCGEN_LOCAL_MODULE_ROOTS",
        "DOCGEN_DEPS_DOCS_URL",
        "DOCGEN_DEPS_DOCS_URLS",
    ):
        digest.update(name.encode() + b"=" + os.environ.get(name, "").encode() + b"\0")
    return digest.hexdigest()


def ordered_modules(root: Path) -> list[str]:
    """Visit dependencies first so one target cannot hide an unbounded cold closure."""
    sources = module_sources(root)
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
    imports = {"Init", "Std", "Lean", "Lake"}
    for path in sources.values():
        imports.update(
            item
            for line in IMPORTS.findall(code_view(path.read_text()))
            for item in line.split()
            if item not in sources
        )
    return sorted(imports)


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
    """Advance verified module batches until complete or the time allowance ends."""
    if seconds <= 0 or batch_size <= 0:
        raise ValueError("batch size and time allowance must be positive")
    build = root / "docbuild" / ".lake" / "build"
    state_path = build / STATE
    identity = input_identity(root)
    modules = ordered_modules(root)
    state = json.loads(state_path.read_text()) if state_path.exists() else {}
    cursor = state.get("cursor", 0) if state.get("identity") == identity else 0
    if not isinstance(cursor, int) or not 0 <= cursor <= len(modules):
        raise ValueError("invalid documentation checkpoint cursor")
    started = cursor
    deadline = time.monotonic() + seconds
    while cursor < len(modules) and time.monotonic() < deadline:
        batch = modules[cursor : cursor + batch_size]
        command = [lake, "build", *(f"+{name}:docInfo" for name in batch)]
        try:
            with batch_checkpoint(build):
                run_build(
                    command, root / "docbuild", max(1, deadline - time.monotonic())
                )
                validate_database(build)
        except subprocess.TimeoutExpired:
            if cursor == started:
                raise RuntimeError(
                    "no batch completed within the time allowance"
                ) from None
            break
        cursor += len(batch)
        state_path.write_text(
            json.dumps({"identity": identity, "cursor": cursor}) + "\n"
        )
        LOGGER.info("Documentation analysis: %s/%s modules", cursor, len(modules))
    return cursor == len(modules)


def require_complete(root: Path) -> None:
    """Refuse to render or publish an incomplete or different source snapshot."""
    build = root / "docbuild" / ".lake" / "build"
    state = json.loads((build / STATE).read_text())
    if state != {"identity": input_identity(root), "cursor": len(module_sources(root))}:
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
