"""Check source-based build reuse and narrowly scoped cache replacement."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from lean_pool.ci_cache import build_revision, obsolete_caches, prepare_cache


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


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Commit Lean sources alongside unrelated Python and documentation files."""
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    for name in ("LeanPool.lean", "LeanPool/A.lean", "scripts/ProjectIndexes.lean"):
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("module\n")
    (tmp_path / "README.md").write_text("Documentation\n")
    _commit(tmp_path)
    return tmp_path


def test_unrelated_commit_reuses_build_identity(repository: Path) -> None:
    """A different commit with the same Lean sources needs no new build upload."""
    before = build_revision(repository)
    (repository / "README.md").write_text("New documentation\n")
    _commit(repository)
    assert build_revision(repository) == before
    assert build_revision(repository, "HEAD^") == before


@pytest.mark.parametrize(
    "name", ["LeanPool.lean", "LeanPool/A.lean", "scripts/ProjectIndexes.lean"]
)
def test_source_change_gets_new_build_identity(repository: Path, name: str) -> None:
    """Pool sources and the index generator each invalidate compiled reuse."""
    before = build_revision(repository)
    (repository / name).write_text("module\n-- change\n")
    _commit(repository)
    assert build_revision(repository) != before
    assert build_revision(repository, "HEAD^") == before


def test_source_addition_and_deletion_change_identity(repository: Path) -> None:
    """Changes to the module inventory count, not just edits to existing files."""
    before = build_revision(repository)
    (repository / "LeanPool/B.lean").write_text("module\n")
    _commit(repository)
    assert build_revision(repository) != before
    (repository / "LeanPool/B.lean").unlink()
    _commit(repository)
    assert build_revision(repository) == before


def test_retention_preserves_other_cache_kinds_platforms_and_prs() -> None:
    """Pruning one build family cannot discard validation or dependency results."""
    keys = [
        ("LeanPoolBuild-v1-Linux-old", "refs/heads/main"),
        ("LeanPoolBuild-v1-Linux-current", "refs/heads/main"),
        ("LeanPoolBuild-v1-Windows-old", "refs/heads/main"),
        ("LeanPoolBuild-v1-Linux-old", "refs/pull/1/merge"),
        ("LeanValidation-v1-Linux-old", "refs/heads/main"),
        ("LeanDependencies-v1-Linux-old", "refs/heads/main"),
    ]
    caches = [
        {"id": index, "key": key, "ref": reference}
        for index, (key, reference) in enumerate(keys)
    ]
    assert obsolete_caches(caches, "LeanPoolBuild-v1-Linux-current") == [0]


def test_prepare_reads_all_pages_and_only_deletes_obsolete_main_entries(
    monkeypatch,
) -> None:
    """The replacement upload can free space without evicting unrelated caches."""
    pages = [
        {
            "actions_caches": [
                {"id": 7, "key": "LeanPoolBuild-v1-Linux-old", "ref": "refs/heads/main"}
            ]
        },
        {
            "actions_caches": [
                {
                    "id": 8,
                    "key": "LeanValidation-v1-Linux-new",
                    "ref": "refs/heads/main",
                }
            ]
        },
    ]
    calls = []
    monkeypatch.setattr(
        subprocess, "check_output", lambda *args, **kwargs: json.dumps(pages)
    )
    monkeypatch.setattr(
        subprocess, "run", lambda command, **kwargs: calls.append(command)
    )
    prepare_cache("owner/repo", "LeanPoolBuild-v1-Linux-new")
    assert calls == [
        ["gh", "api", "--method", "DELETE", "repos/owner/repo/actions/caches/7"]
    ]


def test_unknown_cache_family_is_rejected_before_api_calls(monkeypatch) -> None:
    """An accidental broad cache key must not delete unrelated saved data."""
    monkeypatch.setattr(
        subprocess,
        "check_output",
        lambda *args, **kwargs: pytest.fail("unexpected API call"),
    )
    with pytest.raises(ValueError, match="unsupported cache key"):
        prepare_cache("owner/repo", "unknown")
