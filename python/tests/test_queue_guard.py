"""Verify a queue batch preserves each constituent PR's separation gate."""

import subprocess
from pathlib import Path

import pytest

from lean_pool.queue_guard import group_changes, separation_errors


def test_separate_content_and_infrastructure_prs_can_share_batch(
    tmp_path: Path,
) -> None:
    """Two individually valid PRs stay valid when tested against each other."""

    def git(*args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=tmp_path, text=True).strip()

    git("init")
    git("config", "user.email", "test@example.org")
    git("config", "user.name", "Test")
    (tmp_path / "README.md").write_text("base")
    git("add", ".")
    git("commit", "-m", "base")
    base = git("rev-parse", "HEAD")
    (tmp_path / "LeanPool/projects").mkdir(parents=True)
    (tmp_path / "LeanPool/projects/a.yaml").write_text("slug: a")
    git("add", ".")
    git("commit", "-m", "content PR")
    (tmp_path / "README.md").write_text("documentation")
    git("add", ".")
    git("commit", "-m", "infrastructure PR")
    changes = group_changes(tmp_path, base, "HEAD")
    assert len(changes) == 2
    assert all(not separation_errors(paths) for paths in changes)
    assert separation_errors([path for paths in changes for path in paths])


@pytest.mark.parametrize(
    "paths",
    [
        ["LeanPool/A.lean", "python/lean_pool/quality.py"],
        ["LeanPool.lean"],
        ["LeanPool/A.lean", "LeanPool/projects/nested/a.yaml"],
    ],
)
def test_invalid_single_pr_cannot_hide_in_batch(paths: list[str]) -> None:
    """Queue grouping creates no exemption for mixed changes or the shared root."""
    assert separation_errors(paths)


def test_version_bump_exception_is_preserved() -> None:
    """A proof update alongside pinned version metadata keeps its existing policy."""
    assert not separation_errors(["LeanPool/A.lean", "lean-toolchain"])


def test_lossless_layout_migration_retains_separation() -> None:
    """The legacy base permits its existing content paths but no mixed tooling."""
    files = ["LeanPool.lean", "LeanPool/projects.yml", "LeanPool/projects/a.yaml"]
    assert not separation_errors(files, legacy=True)
    assert separation_errors(files + ["python/lean_pool/quality.py"], legacy=True)
