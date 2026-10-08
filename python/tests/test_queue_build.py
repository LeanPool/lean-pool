"""Queue reuse never replaces checks or overwrites unrelated project passes."""

import json

import pytest

from lean_pool import ci_validation_artifacts, queue_build


def test_only_owned_project_receipts_are_promoted(tmp_path):
    """One PR's old base cannot overwrite another queued project's newer pass."""
    path = tmp_path / ".lake/validation-cache/v1/passes.json"
    path.parent.mkdir(parents=True)
    path.write_text(
        json.dumps(
            {
                "version": 1,
                "receipts": {"lint:LeanPool.B": "new-B", "quality:LeanPool.A": "old-A"},
            }
        )
    )
    queue_build.merge_owned_receipts(
        tmp_path,
        {
            "lint:LeanPool.B": "stale-B",
            "quality:LeanPool.A": "new-A",
            "lint:LeanPool.ABC": "unrelated",
            "lint:LeanPool.A.Part": "new-part",
        },
        ["A"],
    )
    assert json.loads(path.read_text())["receipts"] == {
        "lint:LeanPool.B": "new-B",
        "quality:LeanPool.A": "new-A",
        "lint:LeanPool.A.Part": "new-part",
    }


@pytest.mark.parametrize(
    "same_sources,green_run,expected",
    [(False, 9, []), (True, None, []), (True, 9, [9])],
)
def test_reuse_requires_current_sources_and_a_green_pr_head(
    tmp_path, monkeypatch, same_sources, green_run, expected
):
    """A changed proof or failed prior CI falls back to the complete ordinary build."""
    monkeypatch.setattr(
        queue_build.rebase_fastpath, "git", lambda *args: "Project (#123)\n"
    )
    pull = {
        "head": {"sha": "a" * 40},
        "base": {"repo": {"full_name": "owner/repo"}, "ref": "main", "sha": "b" * 40},
    }
    monkeypatch.setattr(queue_build.rebase_fastpath, "github_json", lambda _: pull)
    monkeypatch.setattr(queue_build.rebase_fastpath, "_exists_at", lambda *args: True)
    monkeypatch.setattr(
        queue_build.ci_pr_build, "sources_match", lambda *args: same_sources
    )
    calls = []

    def successful(repository, number, head):
        calls.append((repository, number, head))
        return green_run

    monkeypatch.setattr(
        queue_build.ci_validation_artifacts, "successful_pr_run", successful
    )
    assert [
        entry["run"]
        for entry in queue_build.candidate_runs(tmp_path, "owner/repo", "base", "head")
    ] == expected
    assert calls == [("owner/repo", 123, "a" * 40)]


def test_latest_queue_attempt_must_succeed(monkeypatch):
    """An older success cannot hide a newer failed check on the same queue head."""

    def github(endpoint):
        if "event=merge_group" in endpoint:
            return {
                "workflow_runs": [
                    {"id": 1, "head_sha": "head", "conclusion": "success"},
                    {"id": 2, "head_sha": "head", "conclusion": "failure"},
                ]
            }
        if "/commits/" in endpoint:
            return []
        raise AssertionError(endpoint)

    monkeypatch.setattr(ci_validation_artifacts, "github_json", github)
    assert ci_validation_artifacts.source_runs("owner/repo", "push", "head", True) == []


@pytest.mark.parametrize("run,expected", [(None, False), (17, True)])
def test_main_uses_only_a_successful_exact_queue_head(
    tmp_path, monkeypatch, run, expected
):
    """A combined archive warms main once; absent evidence keeps normal recovery."""
    calls = []
    monkeypatch.setattr(
        ci_validation_artifacts, "successful_queue_run", lambda repository, head: run
    )
    monkeypatch.setattr(
        queue_build.rebase_fastpath, "restore", lambda *args: calls.append(args)
    )
    assert (
        queue_build.restore_merged_group(tmp_path, "owner/repo", "validated-head")
        is expected
    )
    assert calls == (
        [(tmp_path, "owner/repo", 17, "validated-head")] if expected else []
    )
