"""Refresh ready content PRs without interrupting their existing checks."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


def checks_finished(pull: dict[str, Any]) -> bool:
    """Require observed checks to finish before replacing the checked revision."""
    checks = pull.get("statusCheckRollup")
    return bool(checks) and all(
        check.get("status") == "COMPLETED"
        or check.get("state") in {"SUCCESS", "FAILURE", "ERROR"}
        for check in checks
    )


def select_pulls(pulls: list[dict[str, Any]], number: int = 0) -> list[dict[str, Any]]:
    """Defer drafts and active CI; retain only PRs targeting the maintained main."""
    result = []
    for pull in pulls:
        if (
            (number and pull["number"] != number)
            or pull.get("isDraft", True)
            or pull.get("baseRefName") != "main"
            or pull["headRefName"].startswith("bump/")
            or any(label["name"] == "needs-manual-rebase" for label in pull["labels"])
            or not checks_finished(pull)
        ):
            continue
        result.append(
            {
                "number": pull["number"],
                "branch": pull["headRefName"],
                "head": pull["headRefOid"],
                "repo": (
                    f"{pull['headRepositoryOwner']['login']}/"
                    f"{pull['headRepository']['name']}"
                ),
                "fork": pull["isCrossRepository"],
            }
        )
    return result


def content_only(root: Path, base: str, head: str) -> bool:
    """Keep infrastructure branches stable while independent content merges."""
    changed = subprocess.check_output(
        ["git", "diff", "--name-only", "--no-renames", "-z", f"{base}...{head}"],
        cwd=root,
    ).split(b"\0")
    paths = [path.decode() for path in changed if path]
    return bool(paths) and all(
        path in {"LeanPool.lean", "LeanPool/projects.yml"}
        or (path.startswith("LeanPool/") and path.endswith(".lean"))
        for path in paths
    )


def can_push(pull: dict[str, Any], expected_head: str) -> bool:
    """Recheck races with an author's push or a newly started check."""
    return (
        pull.get("headRefOid") == expected_head
        and not pull.get("isDraft", True)
        and checks_finished(pull)
    )


def main() -> int:
    """Select pending updates or check scope and state before publishing one."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("select", "content", "can-push"))
    parser.add_argument("--number", type=int, default=0)
    parser.add_argument("--base", default="origin/main")
    parser.add_argument("--head", default="HEAD")
    arguments = parser.parse_args()
    if arguments.command == "select":
        print(json.dumps(select_pulls(json.load(sys.stdin), arguments.number)))
        return 0
    if arguments.command == "content":
        return 0 if content_only(Path.cwd(), arguments.base, arguments.head) else 1
    return 0 if can_push(json.load(sys.stdin), arguments.head) else 1


if __name__ == "__main__":
    sys.exit(main())
