"""Recover successful validation receipts independently of large build caches."""

from __future__ import annotations

import argparse
import json
import logging
import os
import subprocess
import tempfile
import zipfile
from pathlib import Path
from urllib.parse import urlencode

from lean_pool.ci_artifacts import github_json

LOGGER = logging.getLogger(__name__)
ARTIFACT = "lean-validation-receipts"
MAXIMUM_BYTES = 32 * 1024 * 1024


def receipts(data: bytes) -> dict:
    """Read receipt metadata; the validation checker still verifies every hash."""
    document = json.loads(data)
    if document.get("version") != 1 or not isinstance(document.get("receipts"), dict):
        raise ValueError("invalid validation receipt artifact")
    return document["receipts"]


def successful_pr_run(repository: str, number: int, head: str) -> int | None:
    """Reuse only the latest successful Lean CI attempt for the merged PR head."""
    query = urlencode({"event": "pull_request", "head_sha": head, "per_page": 100})
    runs = github_json(
        f"repos/{repository}/actions/workflows/lean_action_ci.yml/runs?{query}"
    )["workflow_runs"]
    matches = [
        run
        for run in runs
        if run.get("head_sha") == head
        and (
            not run.get("pull_requests")
            or any(pull.get("number") == number for pull in run["pull_requests"])
        )
    ]
    latest = max(matches, key=lambda run: run["id"], default=None)
    return latest["id"] if latest and latest.get("conclusion") == "success" else None


def source_runs(
    repository: str, event: str, head: str, has_cache: bool
) -> list[tuple[int, bool]]:
    """Promote merged PR passes on main; otherwise recover main's published passes."""
    result = []
    if event == "push":
        queued = successful_queue_run(repository, head)
        if queued is not None:
            result.append((queued, True))
        for pull in github_json(f"repos/{repository}/commits/{head}/pulls"):
            if (
                pull.get("merged_at")
                and pull.get("merge_commit_sha") == head
                and pull.get("base", {}).get("ref") == "main"
            ):
                run = successful_pr_run(repository, pull["number"], pull["head"]["sha"])
                if run is not None:
                    result.append((run, True))
    if not has_cache:
        query = urlencode(
            {"event": "push", "branch": "main", "status": "success", "per_page": 5}
        )
        runs = github_json(
            f"repos/{repository}/actions/workflows/lean_action_ci.yml/runs?{query}"
        )["workflow_runs"]
        result.extend(
            (run["id"], False)
            for run in sorted(runs, key=lambda run: run["id"], reverse=True)
            if run.get("conclusion") == "success" and run.get("head_branch") == "main"
        )
    return result


def successful_queue_run(repository: str, head: str) -> int | None:
    """Find the latest exact-head queue attempt; never hide a newer failure."""
    query = urlencode({"event": "merge_group", "head_sha": head, "per_page": 10})
    runs = github_json(
        f"repos/{repository}/actions/workflows/lean_action_ci.yml/runs?{query}"
    )["workflow_runs"]
    latest = max(
        (run for run in runs if run["head_sha"] == head),
        key=lambda run: run["id"],
        default=None,
    )
    return latest["id"] if latest and latest.get("conclusion") == "success" else None


def download_receipts(repository: str, run: int) -> dict | None:
    """Read one bounded JSON member; never extract artifact paths into the checkout."""
    artifacts = github_json(
        f"repos/{repository}/actions/runs/{run}/artifacts?per_page=100"
    )["artifacts"]
    matches = [
        item for item in artifacts if item["name"] == ARTIFACT and not item["expired"]
    ]
    if not matches:
        return None
    identifier = max(matches, key=lambda item: item["id"])["id"]
    with tempfile.TemporaryDirectory(prefix="lean-validation-") as name:
        archive = Path(name) / "receipts.zip"
        with archive.open("wb") as output:
            subprocess.run(
                ["gh", "api", f"repos/{repository}/actions/artifacts/{identifier}/zip"],
                stdout=output,
                check=True,
                timeout=60,
            )
        with zipfile.ZipFile(archive) as wrapper:
            if wrapper.namelist() != ["passes.json"]:
                raise ValueError("unexpected validation artifact members")
            if wrapper.getinfo("passes.json").file_size > MAXIMUM_BYTES:
                raise ValueError("validation artifact too large")
            return receipts(wrapper.read("passes.json"))


def restore_receipts(
    root: Path, repository: str, event: str, head: str, *, previous_run: int = 0
) -> bool:
    """Missing artifacts leave normal validation intact; reuse never marks a pass."""
    destination = root / ".lake/validation-cache/v1/passes.json"
    try:
        current = receipts(destination.read_bytes())
    except (OSError, ValueError, AttributeError):
        current = {}
    candidates = (
        [(previous_run, True)]
        if previous_run
        else source_runs(repository, event, head, bool(current))
    )
    for run, prefer in candidates:
        try:
            recovered = download_receipts(repository, run)
            if recovered is None:
                continue
            combined = (current | recovered) if prefer else (recovered | current)
            destination.parent.mkdir(parents=True, exist_ok=True)
            temporary = destination.with_suffix(".tmp")
            temporary.write_text(
                json.dumps({"version": 1, "receipts": combined}) + "\n"
            )
            temporary.replace(destination)
            LOGGER.info(
                "Recovered %d saved check results from run %s", len(recovered), run
            )
            return True
        except (
            OSError,
            ValueError,
            AttributeError,
            subprocess.SubprocessError,
            zipfile.BadZipFile,
        ):
            LOGGER.exception(
                "Could not read receipts from %s; regular checks remain", run
            )
    return False


def main() -> None:
    """Restore optional successful receipts before the standard validation steps."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repository", default=os.environ.get("GITHUB_REPOSITORY"), required=False
    )
    parser.add_argument("--event", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--previous-run", type=int, default=0)
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="validation-artifacts: %(message)s")
    try:
        restore_receipts(
            Path.cwd(),
            arguments.repository,
            arguments.event,
            arguments.head,
            previous_run=arguments.previous_run,
        )
    except (OSError, ValueError, AttributeError, KeyError, subprocess.SubprocessError):
        LOGGER.exception("Saved check results unavailable; running normal validation")


if __name__ == "__main__":
    main()
