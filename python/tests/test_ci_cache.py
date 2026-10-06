"""Check source-based build reuse and narrowly scoped cache replacement."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from lean_pool.ci_cache import build_revision, obsolete_caches, prune_cache


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
    "name",
    [
        "scripts/exposition/Extract.lean",
        "scripts/ci/lint-project.lean",
        "scripts/profile.py",
        "LeanPool/projects.yml",
        "LeanPool/A/LICENSE",
    ],
)
def test_unrelated_file_reuses_compiled_build(repository: Path, name: str) -> None:
    """Scripts, project cards, and licenses do not change the pool's compilation."""
    before = build_revision(repository)
    path = repository / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("changed script\n")
    _commit(repository)
    assert build_revision(repository) == before


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


def test_prune_reads_all_pages_and_only_deletes_obsolete_main_entries(
    monkeypatch,
) -> None:
    """A confirmed replacement frees space without deleting unrelated caches."""
    pages = [
        {
            "actions_caches": [
                {"id": 7, "key": "LeanPoolBuild-v1-Linux-old", "ref": "refs/heads/main"}
            ]
        },
        {
            "actions_caches": [
                {
                    "id": 9,
                    "key": "LeanPoolBuild-v1-Linux-new",
                    "ref": "refs/heads/main",
                },
                {
                    "id": 8,
                    "key": "LeanValidation-v1-Linux-new",
                    "ref": "refs/heads/main",
                },
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
    prune_cache("owner/repo", "LeanPoolBuild-v1-Linux-new")
    assert calls == [
        ["gh", "api", "--method", "DELETE", "repos/owner/repo/actions/caches/7"]
    ]


def test_failed_or_missing_replacement_preserves_previous_copy() -> None:
    """An upload failure, or a replacement visible only to a PR, cannot erase main."""
    caches = [
        {"id": 1, "key": "LeanPoolBuild-v1-Linux-old", "ref": "refs/heads/main"},
        {"id": 2, "key": "LeanPoolBuild-v1-Linux-new", "ref": "refs/pull/1/merge"},
    ]
    assert obsolete_caches(caches, "LeanPoolBuild-v1-Linux-new") == []


def test_older_run_cannot_delete_a_newer_run_cache() -> None:
    """Overlapping jobs may prune predecessors but never a newer replacement."""
    caches = [
        {
            "id": index,
            "key": f"LeanPoolBuild-v1-Linux-{index}",
            "ref": "refs/heads/main",
            "created_at": f"2026-10-06T07:0{index}:00Z",
        }
        for index in range(3)
    ]
    assert obsolete_caches(caches, "LeanPoolBuild-v1-Linux-1") == [0]


def test_unknown_cache_family_is_rejected_before_api_calls(monkeypatch) -> None:
    """An accidental broad cache key must not delete unrelated saved data."""
    monkeypatch.setattr(
        subprocess,
        "check_output",
        lambda *args, **kwargs: pytest.fail("unexpected API call"),
    )
    with pytest.raises(ValueError, match="unsupported cache key"):
        prune_cache("owner/repo", "unknown")
