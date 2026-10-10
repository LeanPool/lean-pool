"""Render API documentation for every independent project and verify coverage."""

from __future__ import annotations

import argparse
import logging
import os
import signal
import sqlite3
import subprocess
from pathlib import Path

from lean_pool.indexes import project_modules, structure_errors

logger = logging.getLogger(__name__)


def validate_checkpoint(root: Path) -> None:
    """Flush and check a resumable docInfo database before caching it."""
    build = root / "docbuild/.lake/build"
    database = build / "api-docs.db"
    if not database.is_file() or not database.stat().st_size:
        raise ValueError("documentation checkpoint has no database")
    if not any(
        path.is_file() and path.stat().st_size
        for path in (build / "doc-data").glob("LeanPool*.doc")
    ):
        raise ValueError("documentation checkpoint has no pool documentation data")
    with sqlite3.connect(database) as connection:
        checkpoint = connection.execute("PRAGMA wal_checkpoint(TRUNCATE)").fetchone()
        integrity = connection.execute("PRAGMA quick_check").fetchone()
    if checkpoint is None or checkpoint[0] != 0 or integrity != ("ok",):
        raise ValueError(f"invalid documentation checkpoint: {checkpoint}, {integrity}")


def _stop_build(process: subprocess.Popen) -> None:
    """Stop every writer before validating the shared SQLite checkpoint."""
    for sent_signal in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(process.pid, sent_signal)
        except ProcessLookupError:
            pass
        if sent_signal == signal.SIGTERM:
            try:
                process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                pass
    process.wait()


def prepare_data(root: Path, lake: Path, time_budget: float) -> bool:
    """Prepare incremental docInfo inputs; downstream still builds the full target."""
    if time_budget <= 0:
        raise ValueError("documentation preparation time budget must be positive")
    command = [str(lake), "build", "LeanPool:docInfo"]
    process = subprocess.Popen(command, cwd=root / "docbuild", start_new_session=True)
    try:
        result = process.wait(timeout=time_budget)
    except subprocess.TimeoutExpired:
        _stop_build(process)
        validate_checkpoint(root)
        logger.warning(
            "Preparation time budget reached; full docInfo build still required"
        )
        return False
    if result:
        raise subprocess.CalledProcessError(result, command)
    validate_checkpoint(root)
    return True


def documentation_roots(root: Path) -> list[str]:
    """Select complete public project roots without changing the fixed pool root."""
    errors = structure_errors(root)
    if errors:
        path, message = errors[0]
        raise ValueError(f"{path}: {message}")
    projects = project_modules(root)
    if not projects:
        raise ValueError("no LeanPool projects found")
    return [
        "LeanPool",
        *(f"LeanPool.{project}.Imports" for project in projects),
        "Init",
        "Std",
        "Lake",
        "Lean",
    ]


def validate_site(root: Path, site: Path) -> None:
    """Reject a root-only site or any missing page for a compiled pool source."""
    sources = [root / "LeanPool.lean", *sorted((root / "LeanPool").rglob("*.lean"))]
    required = [
        site / "index.html",
        site / "declarations/declaration-data.bmp",
        *(site / path.relative_to(root).with_suffix(".html") for path in sources),
    ]
    missing = [
        path.relative_to(site)
        for path in required
        if not path.is_file() or not path.stat().st_size
    ]
    if missing:
        sample = ", ".join(str(path) for path in missing[:5])
        raise ValueError(
            f"documentation is missing {len(missing)} required pages/files: {sample}"
        )


def build_site(root: Path, lake: Path) -> None:
    """Generate HTML from verified docInfo using every project's import closure."""
    roots = documentation_roots(root)
    # doc-gen4's library docs facet follows only library roots. LeanPool's fixed
    # root imports no projects, so supply their public roots to fromDb directly.
    subprocess.run(
        [
            str(lake),
            "exe",
            "doc-gen4",
            "fromDb",
            "--build",
            ".lake/build",
            "--manifest",
            ".lake/build/doc-manifest.json",
            ".lake/build/api-docs.db",
            *roots,
        ],
        cwd=root / "docbuild",
        check=True,
    )
    validate_site(root, root / "docbuild/.lake/build/doc")


def main(argv: list[str] | None = None) -> int:
    """Build the complete site or verify an existing documentation artifact."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("prepare", "checkpoint", "build", "validate")
    )
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--lake", type=Path, default=Path.home() / ".elan/bin/lake")
    parser.add_argument("--time-budget", type=float, default=18000)
    arguments = parser.parse_args(argv)
    root = arguments.repo.resolve()
    if arguments.command == "prepare":
        prepare_data(root, arguments.lake.expanduser().resolve(), arguments.time_budget)
    elif arguments.command == "checkpoint":
        validate_checkpoint(root)
    elif arguments.command == "build":
        build_site(root, arguments.lake.expanduser().resolve())
    else:
        documentation_roots(root)
        validate_site(root, root / "docbuild/.lake/build/doc")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
