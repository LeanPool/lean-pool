"""Keep branch updates from cancelling active CI or changing infrastructure PRs."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from lean_pool.rebase_queue import can_push, content_only, select_pulls


@pytest.fixture
def pull() -> dict:
    """A ready content PR whose existing checks have completed."""
    return {
        "number": 42,
        "isDraft": False,
        "baseRefName": "main",
        "headRefName": "feature/project",
        "headRefOid": "a" * 40,
        "headRepositoryOwner": {"login": "owner"},
        "headRepository": {"name": "repo"},
        "isCrossRepository": False,
        "labels": [],
        "statusCheckRollup": [{"status": "COMPLETED", "conclusion": "SUCCESS"}],
    }


@pytest.mark.parametrize(
    "changes",
    [
        {"isDraft": True},
        {"baseRefName": "bump/v4"},
        {"headRefName": "bump/v4"},
        {"labels": [{"name": "needs-manual-rebase"}]},
        {"statusCheckRollup": []},
        {"statusCheckRollup": None},
        {"statusCheckRollup": [{"status": "QUEUED"}]},
        {"statusCheckRollup": [{"status": "IN_PROGRESS"}]},
        {"statusCheckRollup": [{"state": "PENDING"}]},
        {"statusCheckRollup": [{}]},
    ],
)
def test_busy_or_ineligible_pulls_are_deferred(pull: dict, changes: dict) -> None:
    """An update must not interrupt CI, a draft, or a manual/migration branch."""
    assert select_pulls([pull | changes]) == []


def test_ready_pull_is_selected_and_completion_targets_one_pull(pull: dict) -> None:
    """CI completion wakes only the finished PR, preserving other branches."""
    other = pull | {"number": 43}
    assert [item["number"] for item in select_pulls([pull, other], 42)] == [42]
    assert [item["number"] for item in select_pulls([pull, other])] == [42, 43]
    assert select_pulls([pull])[0]["head"] == "a" * 40


def test_completed_failure_can_receive_main_fixes(pull: dict) -> None:
    """Failed CI stays a merge blocker but may benefit from a newer main."""
    pull["statusCheckRollup"] = [{"state": "FAILURE"}]
    assert len(select_pulls([pull])) == 1


def test_author_or_check_races_prevent_publication(pull: dict) -> None:
    """Recheck both the remote revision and active checks before pushing."""
    assert can_push(pull, "a" * 40)
    assert not can_push(pull, "b" * 40)
    assert not can_push(pull | {"isDraft": True}, "a" * 40)
    pull["statusCheckRollup"].append({"status": "IN_PROGRESS"})
    assert not can_push(pull, "a" * 40)


@pytest.mark.parametrize("path", ["LeanPool/A.lean", "README.md", "python/tool.py"])
def test_only_content_branches_are_automatically_updated(tmp_path: Path, path: str):
    """Infrastructure PRs stay stable when unrelated projects merge."""
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=tmp_path, check=True)
    (tmp_path / "LeanPool.lean").write_text("import LeanPool.A\n")
    _commit(tmp_path)
    subprocess.run(["git", "checkout", "-qb", "feature"], cwd=tmp_path, check=True)
    target = tmp_path / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("change\n")
    _commit(tmp_path)
    assert content_only(tmp_path, "main", "HEAD") == path.startswith("LeanPool/")


def _commit(root: Path) -> None:
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "change",
        ],
        cwd=root,
        check=True,
    )
