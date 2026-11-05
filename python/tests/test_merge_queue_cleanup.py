"""Check that only runs for discarded merge groups are cancelled."""

from __future__ import annotations

import subprocess
from typing import Any

import pytest

from lean_pool import merge_queue_cleanup
from lean_pool.merge_queue_cleanup import (
    branch_exists,
    cancel_discarded,
    discarded_runs,
)

LIVE = "gh-readonly-queue/main/pr-2-live"
GONE = "gh-readonly-queue/main/pr-1-gone"
ALSO_GONE = "gh-readonly-queue/main/pr-3-gone"


def _run(identifier: int, branch: str, status: str = "in_progress") -> dict[str, Any]:
    return {"databaseId": identifier, "headBranch": branch, "status": status}


def test_every_missing_branch_is_selected_after_the_first() -> None:
    """A missing ref must not stop the scan before later discarded runs."""
    runs = [_run(1, GONE), _run(2, LIVE), _run(3, ALSO_GONE)]
    assert discarded_runs(runs, 99, lambda branch: branch == LIVE) == [1, 3]


def test_current_completed_and_non_queue_runs_are_kept() -> None:
    """Never cancel this run, finished runs, or runs outside the queue."""
    runs = [
        _run(1, GONE),
        _run(2, GONE, status="completed"),
        _run(3, "feature/branch"),
    ]
    assert discarded_runs(runs, 1, lambda branch: False) == []


@pytest.mark.parametrize(
    ("returncode", "stderr", "expected"),
    [
        (0, "", True),
        (1, "gh: Not Found (HTTP 404)", False),
        (1, "gh: Server Error (HTTP 502)", True),
    ],
)
def test_only_a_definite_404_counts_as_missing(
    monkeypatch: pytest.MonkeyPatch, returncode: int, stderr: str, expected: bool
) -> None:
    """Transient API errors must not cancel a live queue run."""

    def fake_run(*args: Any, **kwargs: Any) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(args, returncode, "", stderr)

    monkeypatch.setattr(subprocess, "run", fake_run)
    assert branch_exists("owner/repository", GONE) is expected


def test_cancel_discarded_cancels_each_missing_run(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Both discarded runs are cancelled even though the first lookup 404s."""
    cancelled: list[list[str]] = []
    monkeypatch.setattr(
        merge_queue_cleanup,
        "queue_runs",
        lambda repository: [_run(1, GONE), _run(2, LIVE), _run(3, ALSO_GONE)],
    )

    def fake_run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        if command[:2] == ["gh", "api"]:
            missing = command[2].endswith(("-gone",))
            return subprocess.CompletedProcess(
                command, 1 if missing else 0, "", "HTTP 404" if missing else ""
            )
        cancelled.append(command)
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(subprocess, "run", fake_run)
    assert cancel_discarded("owner/repository", 99) == [1, 3]
    assert [command[3] for command in cancelled] == ["1", "3"]


def test_ref_timeout_keeps_run_and_scans_later_discarded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An unknown first ref must not hide a later definite missing ref."""
    looked_up: list[str] = []
    cancellation_requests: list[str] = []
    monkeypatch.setattr(
        merge_queue_cleanup,
        "queue_runs",
        lambda repository: [_run(1, GONE), _run(3, ALSO_GONE)],
    )

    def fake_run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        if command[:2] == ["gh", "api"]:
            looked_up.append(command[2])
            if command[2] == f"repos/owner/repository/git/ref/heads/{GONE}":
                raise subprocess.TimeoutExpired(command, 60)
            assert command[2] == f"repos/owner/repository/git/ref/heads/{ALSO_GONE}"
            return subprocess.CompletedProcess(command, 1, "", "HTTP 404")
        assert command[:3] == ["gh", "run", "cancel"]
        cancellation_requests.append(command[3])
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(subprocess, "run", fake_run)
    assert cancel_discarded("owner/repository", 99) == [3]
    assert looked_up == [
        f"repos/owner/repository/git/ref/heads/{GONE}",
        f"repos/owner/repository/git/ref/heads/{ALSO_GONE}",
    ]
    assert cancellation_requests == ["3"]


@pytest.mark.parametrize("failure", ["timeout", "nonzero"])
def test_failed_cancellation_continues_and_returns_only_accepted(
    monkeypatch: pytest.MonkeyPatch, failure: str
) -> None:
    """One failed request must not stop later requests or count as accepted."""
    cancellation_requests: list[str] = []
    monkeypatch.setattr(
        merge_queue_cleanup,
        "queue_runs",
        lambda repository: [_run(1, GONE), _run(3, ALSO_GONE)],
    )

    def fake_run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        if command[:2] == ["gh", "api"]:
            return subprocess.CompletedProcess(command, 1, "", "HTTP 404")
        assert command[:3] == ["gh", "run", "cancel"]
        cancellation_requests.append(command[3])
        if command[3] == "1":
            if failure == "timeout":
                raise subprocess.TimeoutExpired(command, 60)
            return subprocess.CompletedProcess(command, 1, "", "HTTP 403")
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(subprocess, "run", fake_run)
    assert cancel_discarded("owner/repository", 99) == [3]
    assert cancellation_requests == ["1", "3"]
