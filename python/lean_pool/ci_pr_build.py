"""Warm ordinary PR builds without changing their compilation or validation gates."""

from __future__ import annotations

import argparse
import logging
import os
import subprocess
import tarfile
import zipfile
from collections.abc import Iterator
from itertools import chain
from pathlib import Path
from urllib.parse import urlencode

from lean_pool import rebase_fastpath

LOGGER = logging.getLogger(__name__)
RECOVERY_ERRORS = (
    OSError,
    ValueError,
    KeyError,
    subprocess.SubprocessError,
    tarfile.TarError,
    zipfile.BadZipFile,
)


def prior_runs(
    repository: str, number: int, branch: str, current_run: int
) -> Iterator[dict]:
    """Find successful runs of this PR; a later failed attempt supersedes its head."""
    seen = set()
    page = 1
    while True:
        query = urlencode(
            {"event": "pull_request", "branch": branch, "per_page": 100, "page": page}
        )
        runs = rebase_fastpath.github_json(
            f"repos/{repository}/actions/workflows/lean_action_ci.yml/runs?{query}"
        )["workflow_runs"]
        for run in sorted(runs, key=lambda run: run["id"], reverse=True):
            if run["id"] == current_run or not any(
                pull.get("number") == number for pull in run.get("pull_requests", [])
            ):
                continue
            if run["head_sha"] in seen:
                continue
            seen.add(run["head_sha"])
            if run.get("conclusion") == "success":
                yield run
        if len(runs) < 100:
            return
        page += 1


def is_ancestor(root: Path, previous: str, head: str) -> bool:
    """Use only the PR's own reachable history, including ordinary author commits."""
    return bool(rebase_fastpath.SHA.fullmatch(previous)) and (
        subprocess.run(
            ["git", "merge-base", "--is-ancestor", previous, head],
            cwd=root,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        ).returncode
        == 0
    )


def sources_match(root: Path, previous: str, base: str) -> bool:
    """Avoid downloading large artifacts whose tracked Lean inputs already differ."""
    projects = rebase_fastpath._projects(root, base, previous)
    if not all(rebase_fastpath.PROJECT.fullmatch(project) for project in projects):
        return False
    inputs = list(rebase_fastpath.PINNED_INPUTS)
    for project in projects:
        inputs.extend(
            [f"LeanPool/{project}.lean", f":(glob)LeanPool/{project}/**/*.lean"]
        )
    return (
        subprocess.run(
            ["git", "diff", "--quiet", previous, "--", *inputs],
            cwd=root,
            check=False,
        ).returncode
        == 0
    )


def restore_prior_build(
    root: Path,
    repository: str,
    number: int,
    branch: str,
    head: str,
    base: str,
    current_run: int = 0,
) -> bool:
    """Restore matching compiled files; Lake and every normal check still run."""
    if not all(rebase_fastpath.SHA.fullmatch(value) for value in (head, base)):
        raise ValueError("invalid PR revisions")
    candidates = (
        run
        for run in prior_runs(repository, number, branch, current_run)
        if is_ancestor(root, run["head_sha"], head)
    )
    history = next(candidates, None)
    if history is not None:
        try:
            rebase_fastpath.restore_new_main_projects(
                root, repository, history["head_sha"], base, missing_only=True
            )
        except RECOVERY_ERRORS:
            LOGGER.info("Merged project reuse unavailable; checking the PR's build")
    for run in chain(() if history is None else (history,), candidates):
        if not sources_match(root, run["head_sha"], base):
            continue
        try:
            rebase_fastpath.restore(root, repository, run["id"], run["head_sha"])
            LOGGER.info("Restored matching PR build from run %s", run["id"])
            return True
        except RECOVERY_ERRORS:
            LOGGER.info(
                "PR build %s unavailable or changed; trying older run", run["id"]
            )
    LOGGER.info("No matching PR build; Lake will compile the current sources")
    return False


def main() -> None:
    """Perform optional build reuse before the workflow's normal Lake invocation."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", ""))
    parser.add_argument("--number", type=int, required=True)
    parser.add_argument("--branch", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--current-run", type=int, default=0)
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="pr-build: %(message)s")
    try:
        restore_prior_build(
            Path.cwd(),
            arguments.repository,
            arguments.number,
            arguments.branch,
            arguments.head,
            arguments.base,
            arguments.current_run,
        )
    except RECOVERY_ERRORS:
        LOGGER.exception("PR build reuse unavailable; normal compilation remains")


if __name__ == "__main__":
    main()
