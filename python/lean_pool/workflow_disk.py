"""Require runner disk cleanup before any job restores the whole-pool build cache.

The pool build cache (about 8 GB compressed) plus the Lean dependency cache do
not fit in a hosted runner's default free space, so a job that restores it
without first deleting unused preinstalled toolchains dies with "No space left
on device". This check fails Workflow Lint when a job skips that cleanup.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

import yaml

ACTION_PATH = Path(".github/actions/free-disk-space/action.yml")
ACTION_REFERENCE = "./.github/actions/free-disk-space"
POOL_BUILD_CACHE_PREFIX = "LeanPoolBuild-"
CLEANUP_MARKER = "sudo rm -rf /usr/share/dotnet"
RESTORING_ACTIONS = ("actions/cache@", "actions/cache/restore@")


def cleanup_script(root: Path) -> str:
    """Return the shell script the shared free-disk-space action runs."""
    action = yaml.safe_load((root / ACTION_PATH).read_text())
    return action["runs"]["steps"][0]["run"].strip()


def restores_pool_build(step: dict[str, Any]) -> bool:
    """Whether a step downloads the whole-pool build cache onto the runner."""
    if not str(step.get("uses", "")).startswith(RESTORING_ACTIONS):
        return False
    settings = step.get("with") or {}
    if settings.get("lookup-only") in (True, "true"):
        return False
    keys = f"{settings.get('key', '')}\n{settings.get('restore-keys', '')}"
    return POOL_BUILD_CACHE_PREFIX in keys


def frees_disk(step: dict[str, Any], script: str) -> bool:
    """Whether a step runs the shared cleanup, as the action or an exact copy."""
    if step.get("uses") == ACTION_REFERENCE:
        return True
    return str(step.get("run", "")).strip() == script


def job_errors(location: str, steps: list[dict[str, Any]], script: str) -> list[str]:
    """Report a missing, late, or drifted cleanup step in one job."""
    errors = []
    for step in steps:
        run = str(step.get("run", ""))
        if CLEANUP_MARKER in run and run.strip() != script:
            errors.append(
                f"{location}: inline disk cleanup differs from {ACTION_PATH}; "
                f"use `uses: {ACTION_REFERENCE}` or copy its script exactly"
            )
    cleanup_conditions = []
    for step in steps:
        if frees_disk(step, script):
            cleanup_conditions.append(step.get("if"))
        elif restores_pool_build(step):
            # A conditional cleanup only covers a restore with the same condition.
            if not {None, step.get("if")} & set(cleanup_conditions):
                errors.append(
                    f"{location}: step {step.get('name', step['uses'])!r} "
                    f"restores the pool build cache without an earlier cleanup "
                    f"that always runs with it; add `uses: {ACTION_REFERENCE}` "
                    f"after checkout"
                )
            break
    return errors


def workflow_errors(root: Path) -> list[str]:
    """Check every job in every workflow under ``root``."""
    script = cleanup_script(root)
    errors = []
    for path in sorted((root / ".github/workflows").glob("*.y*ml")):
        workflow = yaml.safe_load(path.read_text()) or {}
        for name, job in (workflow.get("jobs") or {}).items():
            location = f"{path.relative_to(root)} job {name}"
            errors.extend(job_errors(location, job.get("steps") or [], script))
    return errors


def main() -> None:
    """Fail when a workflow job restores the pool build without freeing disk."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    arguments = parser.parse_args()
    errors = workflow_errors(arguments.root)
    if errors:
        for error in errors:
            print(f"::error::{error}")
        raise SystemExit(1)
    print("Every job frees runner disk before restoring the pool build cache")


if __name__ == "__main__":
    main()
