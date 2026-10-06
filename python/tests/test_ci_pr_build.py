"""Reusing compiled PR files must preserve ordinary builds and dependency failures."""

from __future__ import annotations

import io
import json
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path

import pytest

from lean_pool import ci_pr_build, rebase_fastpath


def _git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(["git", *arguments], cwd=root, text=True).strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "commit", "-qm", message)
    return _git(root, "rev-parse", "HEAD")


@pytest.fixture
def repository(tmp_path: Path) -> tuple[Path, str, str]:
    """A previous PR build remains unchanged while main edits its dependency."""
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q", "-b", "main")
    _git(root, "config", "user.email", "test@example.com")
    _git(root, "config", "user.name", "Test")
    (root / ".gitignore").write_text(".lake/\n*.tar.gz\n")
    (root / "LeanPool").mkdir()
    (root / "LeanPool/A.lean").write_text(
        "module\n@[expose] public def value : Nat := 1\n"
    )
    (root / "LeanPool/projects.yml").write_text("projects:\n  - slug: a\n")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0-rc3\n")
    (root / "lakefile.toml").write_text(
        'name = "fixture"\nrequiresModuleSystem = true\n'
        '\n[[lean_lib]]\nname = "LeanPool"\n'
    )
    (root / "lake-manifest.json").write_text(
        json.dumps(
            {
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [],
                "name": "fixture",
                "lakeDir": ".lake",
            }
        )
    )
    base = _commit(root, "base")
    _git(root, "checkout", "-qb", "pr")
    (root / "LeanPool/B.lean").write_text(
        "module\npublic import LeanPool.A\n\n"
        "public theorem value_one : value = 1 := rfl\n"
    )
    (root / "LeanPool/projects.yml").write_text("projects:\n  - slug: a\n  - slug: b\n")
    previous = _commit(root, "add B")
    return root, base, previous


def _download(monkeypatch, archive: Path, previous: str) -> list[str]:
    payload = io.BytesIO()
    with zipfile.ZipFile(payload, "w") as wrapper:
        wrapper.writestr(rebase_fastpath.ARCHIVE, archive.read_bytes())
    calls = []
    original_run = subprocess.run

    def api(endpoint):
        calls.append(endpoint)
        if "/runs?" in endpoint:
            return {
                "workflow_runs": [
                    {
                        "id": 7,
                        "head_sha": previous,
                        "conclusion": "success",
                        "pull_requests": [{"number": 42}],
                    }
                ]
            }
        if "/artifacts?" in endpoint:
            return {
                "artifacts": [
                    {"id": 8, "name": rebase_fastpath.ARTIFACT, "expired": False}
                ]
            }
        if endpoint.endswith("/pulls"):
            return []
        pytest.fail(f"unexpected API request: {endpoint}")

    def run(command, **kwargs):
        if command[:2] == ["gh", "api"]:
            kwargs["stdout"].write(payload.getvalue())
            return subprocess.CompletedProcess(command, 0)
        return original_run(command, **kwargs)

    monkeypatch.setattr(rebase_fastpath, "github_json", api)
    monkeypatch.setattr(subprocess, "run", run)
    return calls


def _archive(root: Path, base: str, previous: str) -> tuple[Path, Path]:
    compiled = root / ".lake/build/lib/lean/LeanPool/B.olean"
    compiled.parent.mkdir(parents=True, exist_ok=True)
    compiled.write_text("prior compiled B")
    archive = root / "build.tar.gz"
    rebase_fastpath.pack(root, base, previous, archive)
    compiled.unlink()
    return archive, compiled


def test_metadata_edit_reuses_build_without_skipping_validation(
    repository, monkeypatch
):
    """Metadata edits retain compiled Lean files without writing validation receipts."""
    root, base, previous = repository
    archive, compiled = _archive(root, base, previous)
    (root / "LeanPool/projects.yml").write_text(
        "projects:\n  - slug: a\n  - slug: b\n    description: revised\n"
    )
    head = _commit(root, "revise description")
    _download(monkeypatch, archive, previous)
    assert ci_pr_build.restore_prior_build(root, "owner/repo", 42, "pr", head, base)
    assert compiled.read_text() == "prior compiled B"
    assert (
        (root / "LeanPool/projects.yml").read_text().endswith("description: revised\n")
    )
    assert not (root / ".lake/validation-cache").exists()


@pytest.mark.parametrize(
    "path",
    [
        "LeanPool/B.lean",
        "LeanPool/B/Added.lean",
        "lean-toolchain",
        "lake-manifest.json",
        "lakefile.toml",
    ],
)
def test_changed_source_or_settings_avoid_download(repository, monkeypatch, path):
    """Changed sources and build settings fall back before any artifact download."""
    root, base, previous = repository
    archive, compiled = _archive(root, base, previous)
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("changed input\n")
    head = _commit(root, "edit input")
    calls = _download(monkeypatch, archive, previous)
    assert not ci_pr_build.restore_prior_build(root, "owner/repo", 42, "pr", head, base)
    assert not compiled.exists()
    assert not any("/artifacts" in endpoint for endpoint in calls)


def test_latest_failed_attempt_and_other_pr_are_not_sources(monkeypatch):
    """Only the latest successful attempt of each head belonging to this PR is used."""
    runs = [
        {
            "id": 10,
            "head_sha": "current",
            "conclusion": None,
            "pull_requests": [{"number": 42}],
        },
        {
            "id": 9,
            "head_sha": "a",
            "conclusion": "failure",
            "pull_requests": [{"number": 42}],
        },
        {
            "id": 8,
            "head_sha": "a",
            "conclusion": "success",
            "pull_requests": [{"number": 42}],
        },
        {
            "id": 7,
            "head_sha": "b",
            "conclusion": "success",
            "pull_requests": [{"number": 99}],
        },
        {"id": 6, "head_sha": "c", "conclusion": "success", "pull_requests": []},
        {
            "id": 5,
            "head_sha": "d",
            "conclusion": "success",
            "pull_requests": [{"number": 42}],
        },
    ]
    monkeypatch.setattr(
        rebase_fastpath, "github_json", lambda _: {"workflow_runs": runs}
    )
    assert ci_pr_build.prior_runs("owner/repo", 42, "pr", 10) == [runs[-1]]


def test_unrelated_history_does_not_download(repository, monkeypatch):
    """A successful run on unrelated history cannot supply compiled artifacts."""
    root, base, previous = repository
    _git(root, "checkout", "-q", "main")
    (root / "LeanPool/A.lean").write_text("module\n-- other branch\n")
    unrelated = _commit(root, "other history")
    _git(root, "checkout", "-q", "pr")
    monkeypatch.setattr(
        ci_pr_build, "prior_runs", lambda *args: [{"id": 7, "head_sha": unrelated}]
    )
    monkeypatch.setattr(
        rebase_fastpath, "restore", lambda *args: pytest.fail("unexpected download")
    )
    assert not ci_pr_build.restore_prior_build(
        root, "owner/repo", 42, "pr", previous, base
    )


def test_missing_artifact_preserves_existing_build(repository, monkeypatch):
    """An expired or absent artifact leaves the restored main cache intact."""
    root, base, previous = repository
    compiled = root / ".lake/build/lib/lean/LeanPool/B.olean"
    compiled.parent.mkdir(parents=True)
    compiled.write_text("existing build")
    monkeypatch.setattr(
        ci_pr_build, "prior_runs", lambda *args: [{"id": 7, "head_sha": previous}]
    )
    monkeypatch.setattr(rebase_fastpath, "github_json", lambda _: {"artifacts": []})
    assert not ci_pr_build.restore_prior_build(
        root, "owner/repo", 42, "pr", previous, base
    )
    assert compiled.read_text() == "existing build"


def test_api_failure_leaves_normal_build_path(monkeypatch):
    """Unavailable GitHub evidence cannot prevent the ordinary build from running."""
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "reuse",
            "--number",
            "42",
            "--branch",
            "pr",
            "--head",
            "a" * 40,
            "--base",
            "b" * 40,
        ],
    )

    def unavailable(*args):
        raise subprocess.CalledProcessError(1, "gh")

    monkeypatch.setattr(ci_pr_build, "prior_runs", unavailable)
    ci_pr_build.main()


def test_lake_rebuilds_changed_dependency_and_rejects_invalid_proof(
    repository, monkeypatch
):
    """A real old olean cannot conceal a proof broken by a changed imported module."""
    root, base, previous = repository
    lake = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake"
    if not lake.is_file():
        pytest.skip("pinned Lean toolchain unavailable")
    subprocess.run(
        [str(lake), "build", "LeanPool.B"], cwd=root, check=True, capture_output=True
    )
    archive = root / "build.tar.gz"
    rebase_fastpath.pack(root, base, previous, archive)
    shutil.rmtree(root / ".lake/build")
    _git(root, "checkout", "-q", "main")
    (root / "LeanPool/A.lean").write_text(
        "module\n@[expose] public def value : Nat := 2\n"
    )
    changed_base = _commit(root, "change dependency")
    _git(root, "checkout", "-q", "pr")
    _git(root, "merge", "--no-edit", "main")
    head = _git(root, "rev-parse", "HEAD")
    _download(monkeypatch, archive, previous)
    assert ci_pr_build.restore_prior_build(
        root, "owner/repo", 42, "pr", head, changed_base
    )
    result = subprocess.run(
        [str(lake), "build", "LeanPool.B"], cwd=root, capture_output=True, text=True
    )
    assert result.returncode != 0
    assert "LeanPool.B" in result.stdout + result.stderr
    assert "rfl" in result.stdout + result.stderr


def test_lake_keeps_unchanged_proof_after_metadata_edit(repository, monkeypatch):
    """Lake accepts matching artifacts without recompiling unchanged proofs."""
    root, base, previous = repository
    lake = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake"
    if not lake.is_file():
        pytest.skip("pinned Lean toolchain unavailable")
    subprocess.run(
        [str(lake), "build", "LeanPool.B"], cwd=root, check=True, capture_output=True
    )
    archive = root / "build.tar.gz"
    rebase_fastpath.pack(root, base, previous, archive)
    shutil.rmtree(root / ".lake/build")
    (root / "LeanPool/projects.yml").write_text("projects: []\n")
    head = _commit(root, "metadata update")
    _download(monkeypatch, archive, previous)
    assert ci_pr_build.restore_prior_build(root, "owner/repo", 42, "pr", head, base)
    compiled = root / ".lake/build/lib/lean/LeanPool/B.olean"
    before = compiled.stat().st_mtime_ns
    result = subprocess.run(
        [str(lake), "build", "LeanPool.B"], cwd=root, capture_output=True, text=True
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert compiled.stat().st_mtime_ns == before


def test_untracked_source_inventory_rejected_before_overlay(repository, monkeypatch):
    """The archive's full inventory also rejects an untracked added source."""
    root, base, previous = repository
    archive, compiled = _archive(root, base, previous)
    added = root / "LeanPool/B/Added.lean"
    added.parent.mkdir()
    added.write_text("module\n")
    _download(monkeypatch, archive, previous)
    assert not ci_pr_build.restore_prior_build(
        root, "owner/repo", 42, "pr", previous, base
    )
    assert not compiled.exists()


def test_broken_archive_preserves_existing_build(repository, monkeypatch):
    """An unreadable project archive leaves existing compiled files intact."""
    root, base, previous = repository
    archive, compiled = _archive(root, base, previous)
    archive.write_bytes(b"broken archive")
    compiled.write_text("existing build")
    _download(monkeypatch, archive, previous)
    assert not ci_pr_build.restore_prior_build(
        root, "owner/repo", 42, "pr", previous, base
    )
    assert compiled.read_text() == "existing build"


def test_main_recovery_failure_still_reuses_pr_build(repository, monkeypatch):
    """Missing merged-project evidence does not block a matching own build."""
    root, base, previous = repository
    archive, compiled = _archive(root, base, previous)
    _download(monkeypatch, archive, previous)

    def unavailable(*args, **kwargs):
        raise ValueError("merged artifact unavailable")

    monkeypatch.setattr(rebase_fastpath, "restore_new_main_projects", unavailable)
    assert ci_pr_build.restore_prior_build(root, "owner/repo", 42, "pr", previous, base)
    assert compiled.read_text() == "prior compiled B"
