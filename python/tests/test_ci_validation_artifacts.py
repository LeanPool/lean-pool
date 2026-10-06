"""Recover saved checks without trusting them for changed sources or failed runs."""

from __future__ import annotations

import io
import json
import subprocess
import sys
import zipfile
from pathlib import Path

import pytest

from lean_pool import ci_validation_artifacts as artifacts
from lean_pool.validation_cache import ValidationCache


def _archive(monkeypatch, members: dict[str, bytes]) -> None:
    payload = io.BytesIO()
    with zipfile.ZipFile(payload, "w") as wrapper:
        for name, contents in members.items():
            wrapper.writestr(name, contents)
    monkeypatch.setattr(
        artifacts,
        "github_json",
        lambda _: {
            "artifacts": [{"id": 8, "name": artifacts.ARTIFACT, "expired": False}]
        },
    )

    def download(command, *, stdout, **kwargs):
        assert command[-1].endswith("/artifacts/8/zip")
        stdout.write(payload.getvalue())

    monkeypatch.setattr(artifacts.subprocess, "run", download)


def test_recovered_passes_still_recheck_changed_sources(tmp_path: Path, monkeypatch):
    """Transporting a real pass receipt cannot bypass its original dependency checks."""
    source = tmp_path / "LeanPool/A.lean"
    source.parent.mkdir()
    source.write_text("def a := 1\n")
    inventory = tmp_path / ".lake/build/ir/LeanPool/A.setup.json"
    inventory.parent.mkdir(parents=True)
    inventory.write_text(json.dumps({"name": "LeanPool.A", "importArts": {}}))
    directory = tmp_path / ".lake/validation-cache/v1"
    cache = ValidationCache(tmp_path, directory)
    assert cache.check("lint", ["LeanPool.A"], lambda: []) == []
    cache.save()
    saved = (directory / "passes.json").read_bytes()
    (directory / "passes.json").unlink()
    _archive(monkeypatch, {"passes.json": saved})
    monkeypatch.setattr(artifacts, "source_runs", lambda *args: [(1, False)])
    assert artifacts.restore_receipts(tmp_path, "owner/repo", "pull_request", "head")
    cache = ValidationCache(tmp_path, directory)
    assert cache.check("lint", ["LeanPool.A"], lambda: ["unexpected recheck"]) == []
    source.write_text("def a := 2\n")
    cache = ValidationCache(tmp_path, directory)
    assert cache.check("lint", ["LeanPool.A"], lambda: ["must recheck"]) == [
        "must recheck"
    ]


@pytest.mark.parametrize("prefer, expected", [(True, "new"), (False, "old")])
def test_promoted_pr_passes_replace_old_main_results(
    tmp_path, monkeypatch, prefer, expected
):
    """Main uses a merged PR's newer results; fallback preserves existing PR results."""
    destination = tmp_path / ".lake/validation-cache/v1/passes.json"
    destination.parent.mkdir(parents=True)
    destination.write_text(json.dumps({"version": 1, "receipts": {"check": "old"}}))
    _archive(
        monkeypatch,
        {
            "passes.json": json.dumps(
                {"version": 1, "receipts": {"check": "new"}}
            ).encode()
        },
    )
    monkeypatch.setattr(artifacts, "source_runs", lambda *args: [(1, prefer)])
    assert artifacts.restore_receipts(tmp_path, "owner/repo", "push", "head")
    assert json.loads(destination.read_text())["receipts"]["check"] == expected


def test_warm_pr_does_not_query_artifact_api(monkeypatch):
    """Normal cached PRs need no extra metadata requests or downloads."""
    monkeypatch.setattr(
        artifacts, "github_json", lambda _: pytest.fail("unexpected API request")
    )
    assert artifacts.source_runs("owner/repo", "pull_request", "head", True) == []


def test_verified_rebase_carries_prior_results_without_run_search(
    tmp_path, monkeypatch
):
    """The existing rebase eligibility check supplies its exact successful run."""
    _archive(monkeypatch, {"passes.json": b'{"version": 1, "receipts": {"prior": {}}}'})
    monkeypatch.setattr(
        artifacts, "source_runs", lambda *args: pytest.fail("unexpected run search")
    )
    assert artifacts.restore_receipts(
        tmp_path, "owner/repo", "pull_request", "head", previous_run=42
    )
    saved = tmp_path / ".lake/validation-cache/v1/passes.json"
    assert json.loads(saved.read_text())["receipts"] == {"prior": {}}


def test_only_associated_merged_main_pull_is_promoted(monkeypatch):
    """An open PR, different merge commit, or migration branch is not a source."""
    valid = {
        "number": 42,
        "merged_at": "now",
        "merge_commit_sha": "merge",
        "base": {"ref": "main"},
        "head": {"sha": "head"},
    }

    def response(endpoint):
        if endpoint.endswith("/commits/merge/pulls"):
            return [
                valid | {"merged_at": None},
                valid | {"merge_commit_sha": "other"},
                valid | {"base": {"ref": "bump/v4"}},
                valid,
            ]
        assert "head_sha=head" in endpoint
        return {
            "workflow_runs": [
                {
                    "id": 8,
                    "head_sha": "head",
                    "pull_requests": [],
                    "conclusion": "success",
                }
            ]
        }

    monkeypatch.setattr(artifacts, "github_json", response)
    assert artifacts.source_runs("owner/repo", "push", "merge", True) == [(8, True)]


def test_failed_latest_attempt_blocks_older_pass_promotion(monkeypatch):
    """A rerun failure cannot be hidden by an older successful attempt."""
    runs = [
        {"id": 8, "head_sha": "head", "conclusion": "success"},
        {"id": 9, "head_sha": "head", "conclusion": "failure"},
    ]
    monkeypatch.setattr(artifacts, "github_json", lambda _: {"workflow_runs": runs})
    assert artifacts.successful_pr_run("owner/repo", 42, "head") is None


def test_missing_cache_uses_only_successful_main_runs(monkeypatch):
    """Sibling PR artifacts are never selected as default-branch results."""
    runs = [
        {"id": 7, "head_branch": "main", "conclusion": "success"},
        {"id": 8, "head_branch": "main", "conclusion": "success"},
        {"id": 9, "head_branch": "feature", "conclusion": "success"},
        {"id": 10, "head_branch": "main", "conclusion": "failure"},
    ]
    monkeypatch.setattr(artifacts, "github_json", lambda _: {"workflow_runs": runs})
    assert artifacts.source_runs("owner/repo", "pull_request", "head", False) == [
        (8, False),
        (7, False),
    ]


@pytest.mark.parametrize(
    "members",
    [
        {"../passes.json": b"{}"},
        {"passes.json": b"broken"},
        {"passes.json": b'{"version": 2, "receipts": {}}'},
        {"passes.json": b'{"version": 1, "receipts": []}'},
    ],
)
def test_bad_download_preserves_existing_receipts(tmp_path, monkeypatch, members):
    """Rejected artifacts do not discard existing passes or alter build files."""
    destination = tmp_path / ".lake/validation-cache/v1/passes.json"
    destination.parent.mkdir(parents=True)
    existing = b'{"version": 1, "receipts": {"old": {}}}'
    destination.write_bytes(existing)
    _archive(monkeypatch, members)
    monkeypatch.setattr(artifacts, "source_runs", lambda *args: [(1, True)])
    assert not artifacts.restore_receipts(tmp_path, "owner/repo", "push", "head")
    assert destination.read_bytes() == existing


def test_oversized_receipts_are_rejected(monkeypatch):
    """Unexpectedly large content never becomes a validation input file."""
    _archive(monkeypatch, {"passes.json": b'{"version": 1, "receipts": {}}'})
    monkeypatch.setattr(artifacts, "MAXIMUM_BYTES", 1)
    with pytest.raises(ValueError, match="too large"):
        artifacts.download_receipts("owner/repo", 1)


def test_api_limit_keeps_standard_validation_path(monkeypatch):
    """A transient API problem is a reuse miss rather than a new gate failure."""
    monkeypatch.setattr(
        sys,
        "argv",
        ["receipts", "--repository", "owner/repo", "--event", "push", "--head", "head"],
    )

    def unavailable(*args):
        raise subprocess.CalledProcessError(1, "gh")

    monkeypatch.setattr(artifacts, "source_runs", unavailable)
    artifacts.main()
