"""Reuse verified constituent PR outputs while retaining the complete queue build."""

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import subprocess
from pathlib import Path

from lean_pool import ci_pr_build, ci_validation_artifacts, rebase_fastpath

LOGGER = logging.getLogger(__name__)


def candidate_runs(root: Path, repository: str, base: str, head: str) -> list[dict]:
    """Find green PR heads named by GitHub's squash-generated queue commits."""
    messages = rebase_fastpath.git(root, "log", "--format=%s", f"{base}..{head}")
    numbers = sorted(
        {int(n) for n in re.findall(r"\(#(\d+)\)$", messages, re.MULTILINE)}
    )
    result = []
    for number in numbers:
        pull = rebase_fastpath.github_json(f"repos/{repository}/pulls/{number}")
        if (
            pull["base"]["repo"]["full_name"] != repository
            or pull["base"]["ref"] != "main"
        ):
            continue
        previous = pull["head"]["sha"]
        if not rebase_fastpath.SHA.fullmatch(previous):
            continue
        if not rebase_fastpath._exists_at(root, previous, "lakefile.toml"):
            subprocess.run(["git", "fetch", "origin", previous], cwd=root, check=True)
        run = ci_validation_artifacts.successful_pr_run(repository, number, previous)
        if run is not None and ci_pr_build.sources_match(
            root, previous, pull["base"]["sha"]
        ):
            result.append({"run": run, "head": previous, "base": pull["base"]["sha"]})
    return result


def merge_owned_receipts(root: Path, incoming: dict, projects: list[str]) -> None:
    """Promote only a PR's own units; existing hash validation remains authoritative."""
    path = root / ".lake/validation-cache/v1/passes.json"
    try:
        current = ci_validation_artifacts.receipts(path.read_bytes())
    except (OSError, ValueError):
        current = {}
    for key, value in incoming.items():
        module = key.partition(":")[2]
        if any(
            module == f"LeanPool.{p}" or module.startswith(f"LeanPool.{p}.")
            for p in projects
        ):
            current[key] = value
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps({"version": 1, "receipts": current}) + "\n")
    temporary.replace(path)


def restore_merged_group(root: Path, repository: str, head: str) -> bool:
    """Restore one combined queue archive on main before its cache is published."""
    run = ci_validation_artifacts.successful_queue_run(repository, head)
    if run is None:
        return False
    rebase_fastpath.restore(root, repository, run, head)
    return True


def main() -> None:
    """Try queue-specific recovery before ordinary compilation or validation."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", ""))
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--receipts", action="store_true")
    parser.add_argument("--merged", action="store_true")
    args = parser.parse_args()
    root = Path.cwd()
    logging.basicConfig(level=logging.INFO)
    if args.merged:
        try:
            restored = restore_merged_group(root, args.repository, args.head)
        except ci_pr_build.RECOVERY_ERRORS:
            LOGGER.exception("Merged queue archive unavailable; use ordinary recovery")
            restored = False
        raise SystemExit(0 if restored else 1)
    try:
        candidates = candidate_runs(root, args.repository, args.base, args.head)
    except ci_pr_build.RECOVERY_ERRORS:
        LOGGER.exception("Queue recovery unavailable; ordinary checks remain")
        return
    for candidate in candidates:
        try:
            if args.receipts:
                incoming = ci_validation_artifacts.download_receipts(
                    args.repository, candidate["run"]
                )
                if incoming is not None:
                    projects = rebase_fastpath._projects(
                        root, candidate["base"], candidate["head"]
                    )
                    merge_owned_receipts(root, incoming, projects)
            else:
                rebase_fastpath.restore(
                    root, args.repository, candidate["run"], candidate["head"]
                )
            LOGGER.info("Recovered queued PR outputs from run %s", candidate["run"])
        except ci_pr_build.RECOVERY_ERRORS:
            LOGGER.exception(
                "Candidate unavailable; normal compilation and validation remain"
            )


if __name__ == "__main__":
    main()
