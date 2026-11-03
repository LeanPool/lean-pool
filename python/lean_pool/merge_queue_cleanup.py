"""Cancel merge-queue CI runs whose queue entry GitHub has already discarded.

A push to main from outside the queue makes GitHub rebuild every queued group
and delete the old groups' `gh-readonly-queue/...` refs, but runs started for
those refs keep building. A run whose ref no longer exists can never merge.
"""

from __future__ import annotations

import argparse
import json
import logging
import subprocess
from collections.abc import Callable
from typing import Any

LOGGER = logging.getLogger(__name__)
WORKFLOW = "lean_action_ci.yml"


def discarded_runs(
    runs: list[dict[str, Any]],
    current_run_id: int,
    branch_exists: Callable[[str], bool],
) -> list[int]:
    """Select unfinished queue runs, other than this one, whose branch is gone."""
    return [
        run["databaseId"]
        for run in runs
        if run.get("status") != "completed"
        and run.get("databaseId") != current_run_id
        and str(run.get("headBranch", "")).startswith("gh-readonly-queue/")
        and not branch_exists(run["headBranch"])
    ]


def branch_exists(repository: str, branch: str) -> bool:
    """Report a branch as missing only on a definite 404, never on other errors."""
    try:
        result = subprocess.run(
            ["gh", "api", f"repos/{repository}/git/ref/heads/{branch}"],
            capture_output=True,
            text=True,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        LOGGER.warning("Timed out looking up %s; keeping its run", branch)
        return True
    if result.returncode == 0:
        return True
    if "HTTP 404" in result.stderr:
        return False
    LOGGER.warning("Could not look up %s: %s", branch, result.stderr.strip())
    return True


def queue_runs(repository: str) -> list[dict[str, Any]]:
    """List recent merge-group runs of the Lean CI workflow."""
    output = subprocess.check_output(
        [
            "gh",
            "run",
            "list",
            "--repo",
            repository,
            "--workflow",
            WORKFLOW,
            "--event",
            "merge_group",
            "--limit",
            "100",
            "--json",
            "databaseId,status,headBranch",
        ],
        text=True,
        timeout=60,
    )
    return json.loads(output)


def cancel_discarded(repository: str, current_run_id: int) -> list[int]:
    """Request cancellation of discarded runs and return accepted request IDs."""
    discarded = discarded_runs(
        queue_runs(repository),
        current_run_id,
        lambda branch: branch_exists(repository, branch),
    )
    accepted: list[int] = []
    for run_id in discarded:
        try:
            result = subprocess.run(
                ["gh", "run", "cancel", str(run_id), "--repo", repository],
                check=False,
                capture_output=True,
                text=True,
                timeout=60,
            )
        except subprocess.TimeoutExpired:
            LOGGER.warning("Timed out requesting cancellation of run %s", run_id)
            continue
        if result.returncode != 0:
            LOGGER.warning(
                "Could not request cancellation of run %s: %s",
                run_id,
                result.stderr.strip(),
            )
            continue
        LOGGER.info(
            "Requested cancellation of run %s: its merge group was discarded", run_id
        )
        accepted.append(run_id)
    return accepted


def main() -> None:
    """Cancel discarded merge-group runs for one repository."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--current-run-id", type=int, required=True)
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="queue: %(message)s")
    cancel_discarded(arguments.repository, arguments.current_run_id)


if __name__ == "__main__":
    main()
