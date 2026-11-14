"""Label pull requests stale after a week open and close them after three.

The policy is by age, not inactivity: review bots comment on every PR, so
an inactivity clock would never run out. A PR is labelled ``stale`` once it
has been open :data:`STALE_AFTER`, and closed once it has been open
:data:`CLOSE_AFTER` *and* has carried the label for at least
:data:`MINIMUM_LABELLED`, so every PR gets a week's warning, including
PRs that were already old when this policy started.

Run ``python -m lean_pool.stale_pull_requests --repository OWNER/NAME``
(``--dry-run`` prints the actions without taking them). It needs an
authenticated ``gh`` CLI.
"""

from __future__ import annotations

import argparse
import json
import logging
import subprocess
from dataclasses import dataclass
from datetime import UTC, datetime, timedelta

LOGGER = logging.getLogger(__name__)

STALE_LABEL = "stale"
EXEMPT_LABEL = "pinned"
STALE_AFTER = timedelta(days=7)
CLOSE_AFTER = timedelta(days=21)
MINIMUM_LABELLED = timedelta(days=7)

STALE_MESSAGE = (
    "This PR has been open for 7 days and is now marked `stale`. "
    "Open PRs are closed automatically once they are 21 days old "
    "(and have been marked stale for at least 7 days)."
)
CLOSE_MESSAGE = (
    "Closing this PR: it has been open for 21 days. "
    "Reopen or resubmit it if it is still wanted."
)


@dataclass(frozen=True)
class PullRequest:
    """The fields of an open pull request the policy reads."""

    number: int
    created_at: datetime
    labels: frozenset[str]


def decide(
    pull_request: PullRequest, labelled_at: datetime | None, now: datetime
) -> str | None:
    """Return ``"label"``, ``"close"`` or ``None`` for one open pull request.

    Args:
        pull_request: The open pull request.
        labelled_at: When the ``stale`` label was last added, if it is present.
        now: The current time.

    Returns:
        The action to take, or ``None`` when the PR is left alone.
    """
    if EXEMPT_LABEL in pull_request.labels:
        return None
    age = now - pull_request.created_at
    if STALE_LABEL not in pull_request.labels:
        return "label" if age >= STALE_AFTER else None
    labelled_long_enough = labelled_at is None or now - labelled_at >= MINIMUM_LABELLED
    if age >= CLOSE_AFTER and labelled_long_enough:
        return "close"
    return None


def _gh(*arguments: str) -> str:
    return subprocess.run(
        ["gh", *arguments], check=True, capture_output=True, text=True
    ).stdout


def _parse_time(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def open_pull_requests(repository: str) -> list[PullRequest]:
    """Return every open pull request in ``repository``."""
    rows = json.loads(
        _gh(
            "pr",
            "list",
            "--repo",
            repository,
            "--state",
            "open",
            "--limit",
            "1000",
            "--json",
            "number,createdAt,labels",
        )
    )
    return [
        PullRequest(
            number=row["number"],
            created_at=_parse_time(row["createdAt"]),
            labels=frozenset(label["name"] for label in row["labels"]),
        )
        for row in rows
    ]


def stale_labelled_at(repository: str, number: int) -> datetime | None:
    """Return when the ``stale`` label was last added to PR ``number``."""
    events = json.loads(
        _gh(
            "api",
            "--paginate",
            "--slurp",
            f"repos/{repository}/issues/{number}/events?per_page=100",
        )
    )
    times = [
        _parse_time(event["created_at"])
        for page in events
        for event in page
        if event.get("event") == "labeled"
        and (event.get("label") or {}).get("name") == STALE_LABEL
    ]
    return max(times, default=None)


def apply(repository: str, number: int, action: str, dry_run: bool) -> None:
    """Label or close one pull request, with an explanatory comment."""
    LOGGER.info("PR #%d: %s%s", number, action, " (dry run)" if dry_run else "")
    if dry_run:
        return
    target = str(number)
    if action == "label":
        _gh("pr", "edit", target, "--repo", repository, "--add-label", STALE_LABEL)
        _gh("pr", "comment", target, "--repo", repository, "--body", STALE_MESSAGE)
    elif action == "close":
        _gh("pr", "close", target, "--repo", repository, "--comment", CLOSE_MESSAGE)


def main(argv: list[str] | None = None) -> int:
    """Apply the stale policy to every open pull request."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repository", required=True, help="OWNER/NAME")
    parser.add_argument("--dry-run", action="store_true")
    arguments = parser.parse_args(argv)
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    now = datetime.now(UTC)
    for pull_request in open_pull_requests(arguments.repository):
        labelled_at = None
        if STALE_LABEL in pull_request.labels:
            labelled_at = stale_labelled_at(arguments.repository, pull_request.number)
        action = decide(pull_request, labelled_at, now)
        if action:
            apply(arguments.repository, pull_request.number, action, arguments.dry_run)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
