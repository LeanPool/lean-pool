"""Validate exact-tree build reuse and safe fallback for unavailable artifacts."""

from __future__ import annotations

import io
import json
import os
import subprocess
import tarfile
import zipfile
from pathlib import Path

import pytest

from lean_pool import ci_artifacts


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Create a committed source tree with an ignored synthetic Lake build."""
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        (tmp_path / name).write_text(name)
    (tmp_path / ".gitignore").write_text(".lake/\n*.tar.gz\n")
    (tmp_path / ".lake/build/lib/lean").mkdir(parents=True)
    (tmp_path / ".lake/build/lib/lean/LeanPool.olean").write_bytes(b"compiled")
    for command in (
        ["init", "-q"],
        ["add", "."],
        [
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "initial",
        ],
    ):
        subprocess.run(["git", *command], cwd=tmp_path, check=True)
    return tmp_path


def test_build_round_trip(repository: Path) -> None:
    """Matching output replaces the old build completely, including removed modules."""
    archive = repository / "build.tar.gz"
    ci_artifacts.pack_build(repository, archive)
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    output.write_bytes(b"old")
    stale = output.with_name("Removed.olean")
    stale.touch()
    assert ci_artifacts.restore_build(repository, archive)
    assert output.read_bytes() == b"compiled"
    assert not stale.exists()


def test_mismatched_configuration_preserves_current_build(repository: Path) -> None:
    """An incompatible toolchain never replaces the fallback build."""
    archive = repository / "build.tar.gz"
    ci_artifacts.pack_build(repository, archive)
    (repository / "lean-toolchain").write_text("other version")
    assert not ci_artifacts.restore_build(repository, archive)
    assert (
        repository / ".lake/build/lib/lean/LeanPool.olean"
    ).read_bytes() == b"compiled"


def test_mismatched_tree_preserves_current_build(repository: Path) -> None:
    """A different source tree cannot reuse a same-toolchain artifact."""
    archive = repository / "build.tar.gz"
    ci_artifacts.pack_build(repository, archive)
    (repository / "Added.lean").write_text("-- new source\n")
    subprocess.run(["git", "add", "Added.lean"], cwd=repository, check=True)
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
        cwd=repository,
        check=True,
    )
    assert not ci_artifacts.restore_build(repository, archive)


def test_pack_rejects_dirty_checkout(repository: Path) -> None:
    """The producer cannot label modified build inputs with the committed tree."""
    (repository / "lakefile.toml").write_text("changed options")
    with pytest.raises(subprocess.CalledProcessError):
        ci_artifacts.pack_build(repository, repository / "build.tar.gz")


@pytest.mark.parametrize(
    ("name", "kind"),
    [
        ("../escape", tarfile.REGTYPE),
        ("/tmp/escape", tarfile.REGTYPE),
        (".lake/build/../../escape", tarfile.REGTYPE),
        ("LeanPool.lean", tarfile.REGTYPE),
        (".lake/build/link", tarfile.SYMTYPE),
        (".lake/build/link", tarfile.LNKTYPE),
    ],
)
def test_unexpected_archive_member_rejected(repository: Path, name: str, kind) -> None:
    """No archive path, symlink, or hardlink can escape the build directory."""
    destination = repository / "build.tar.gz"
    with tarfile.open(destination, "w:gz") as archive:
        payload = json.dumps(ci_artifacts.build_identity(repository)).encode()
        manifest = tarfile.TarInfo(ci_artifacts.MANIFEST_NAME)
        manifest.size = len(payload)
        archive.addfile(manifest, io.BytesIO(payload))
        member = tarfile.TarInfo(name)
        member.type = kind
        member.linkname = "../../../escape"
        archive.addfile(member)
    with pytest.raises(ValueError, match="Unexpected build archive member"):
        ci_artifacts.restore_build(repository, destination)
    assert (repository / ".lake/build/lib/lean/LeanPool.olean").exists()


def test_missing_run_falls_back(repository: Path, monkeypatch) -> None:
    """Docs-only changes and disabled CI retain the regular Lake build path."""
    monkeypatch.setattr(ci_artifacts, "matching_run", lambda *args: None)
    assert not ci_artifacts.reuse_build(repository, "owner/repo", "head", "push", 0)


def test_pull_request_does_not_wait_for_unpublished_build(
    repository: Path, monkeypatch
):
    """PR producers omit full build artifacts, so consumers use Lake immediately."""

    def unexpected_query(*args):
        pytest.fail("PR build reuse must not query or wait for an unpublished artifact")

    monkeypatch.setattr(ci_artifacts, "github_json", unexpected_query)
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    before = output.read_bytes()
    assert not ci_artifacts.reuse_build(
        repository, "owner/repo", "head", "pull_request", 7200
    )
    assert output.read_bytes() == before


def test_api_error_falls_back(repository: Path, monkeypatch) -> None:
    """Artifact API errors are an optimization miss rather than a docs failure."""

    def unavailable(*args):
        raise subprocess.CalledProcessError(1, "gh")

    monkeypatch.setattr(ci_artifacts, "matching_run", unavailable)
    assert not ci_artifacts.reuse_build(repository, "owner/repo", "head", "push", 0)


def test_matching_run_queries_exact_head_and_event(monkeypatch) -> None:
    """Concurrent PR/push runs cannot accidentally select another workflow's outputs."""
    endpoints = []

    def response(endpoint):
        endpoints.append(endpoint)
        return {"workflow_runs": [{"id": 1}, {"id": 5}]}

    monkeypatch.setattr(ci_artifacts, "github_json", response)
    assert ci_artifacts.matching_run("owner/repo", "abc123", "pull_request") == {
        "id": 5
    }
    assert "lean_action_ci.yml/runs?head_sha=abc123&event=pull_request&" in endpoints[0]


@pytest.mark.parametrize("status", ["completed", "in_progress"])
def test_wait_ends_on_completed_run_or_deadline(monkeypatch, status: str) -> None:
    """Missing artifacts cannot cause an unbounded wait."""

    def response(endpoint):
        return {"artifacts": []} if "/artifacts?" in endpoint else {"status": status}

    monkeypatch.setattr(ci_artifacts, "github_json", response)
    assert ci_artifacts.wait_for_artifact("owner/repo", {"id": 1}, 0) is None


def test_artifact_available_before_quality_finishes(monkeypatch) -> None:
    """Compilation output can be consumed while later checks are still running."""

    def response(endpoint):
        assert "/artifacts?" in endpoint
        return {"artifacts": [{"id": 8, "name": "lean-pool-build", "expired": False}]}

    monkeypatch.setattr(ci_artifacts, "github_json", response)
    assert ci_artifacts.wait_for_artifact("owner/repo", {"id": 1}, 0) == 8


@pytest.mark.parametrize("extension", ["gz", "zst"])
def test_streamed_build_replaces_directory_without_copying(
    repository: Path, monkeypatch, extension: str
) -> None:
    """Both compression formats restore all files without a second directory copy."""
    archive = repository / f"build.tar.{extension}"
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    ci_artifacts.pack_build(repository, archive)
    output.write_bytes(b"old")
    monkeypatch.setattr(
        ci_artifacts.shutil,
        "copytree",
        lambda *args, **kwargs: pytest.fail("unexpected second build copy"),
    )
    assert ci_artifacts.restore_build(repository, archive)
    assert output.read_bytes() == b"compiled"


@pytest.mark.parametrize("extension", ["gz", "zst"])
def test_truncated_compression_preserves_current_build(
    repository: Path, extension: str
) -> None:
    """Reject incomplete compressed files before installing the staged build."""
    archive = repository / f"build.tar.{extension}"
    ci_artifacts.pack_build(repository, archive)
    archive.write_bytes(archive.read_bytes()[:-8])
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    output.write_bytes(b"original build")
    with pytest.raises((subprocess.SubprocessError, tarfile.TarError, EOFError)):
        ci_artifacts.restore_build(repository, archive)
    assert output.read_bytes() == b"original build"
    assert not list((repository / ".lake").glob("lean-ci-build-*"))


def test_invalid_member_after_valid_output_preserves_current_build(repository: Path):
    """A later invalid path cannot install an otherwise valid partial build."""
    destination = repository / "build.tar.gz"
    with tarfile.open(destination, "w:gz") as archive:
        for name, payload in (
            (
                ci_artifacts.MANIFEST_NAME,
                json.dumps(ci_artifacts.build_identity(repository)).encode(),
            ),
            (".lake/build/lib/lean/LeanPool.olean", b"replacement"),
            ("../escape", b"invalid"),
        ):
            member = tarfile.TarInfo(name)
            member.size = len(payload)
            archive.addfile(member, io.BytesIO(payload))
    with pytest.raises(ValueError, match="Unexpected build archive member"):
        ci_artifacts.restore_build(repository, destination)
    assert (
        repository / ".lake/build/lib/lean/LeanPool.olean"
    ).read_bytes() == b"compiled"


def test_unchanged_files_share_disk_until_install(repository: Path, monkeypatch):
    """Staging consumes space for changed files while preserving original metadata."""
    archive = repository / "build.tar.gz"
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    ci_artifacts.pack_build(repository, archive)
    archived_time = output.stat().st_mtime_ns
    os.utime(output, ns=(1_000_000_000, 1_000_000_000))
    original = ci_artifacts._extract_build

    def extract(root, contents, temporary, reused):
        result = original(root, contents, temporary, reused)
        staged = temporary / output.relative_to(repository)
        assert staged.samefile(output)
        assert output.stat().st_mtime_ns == 1_000_000_000
        assert output.stat().st_nlink == 2
        return result

    monkeypatch.setattr(ci_artifacts, "_extract_build", extract)
    assert ci_artifacts.restore_build(repository, archive)
    assert output.stat().st_mtime == pytest.approx(archived_time / 1_000_000_000)
    assert output.stat().st_nlink == 1


def test_duplicate_member_cannot_overwrite_shared_cache(repository: Path):
    """Reject duplicate paths before extraction could write through a hard link."""
    destination = repository / "build.tar.gz"
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    metadata = output.stat()
    with tarfile.open(destination, "w:gz") as archive:
        for name, payload in (
            (
                ci_artifacts.MANIFEST_NAME,
                json.dumps(ci_artifacts.build_identity(repository)).encode(),
            ),
            (".lake/build/lib/lean/LeanPool.olean", b"compiled"),
            (".lake/build/lib/lean/./LeanPool.olean", b"changed"),
        ):
            member = tarfile.TarInfo(name)
            member.size = len(payload)
            archive.addfile(member, io.BytesIO(payload))
    with pytest.raises(ValueError, match="Unexpected build archive member"):
        ci_artifacts.restore_build(repository, destination)
    assert output.read_bytes() == b"compiled"
    assert output.stat().st_mtime_ns == metadata.st_mtime_ns
    assert output.stat().st_nlink == 1


@pytest.mark.parametrize(
    "name", [ci_artifacts.ARCHIVE_NAME, ci_artifacts.LEGACY_ARCHIVE_NAME]
)
def test_download_accepts_current_and_previous_compression(
    repository: Path, monkeypatch, name: str
) -> None:
    """Documentation can consume builds produced on either side of the rollout."""
    archive = repository / name
    ci_artifacts.pack_build(repository, archive)
    zipped = io.BytesIO()
    with zipfile.ZipFile(zipped, "w") as bundle:
        bundle.write(archive, arcname=name)
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    output.write_bytes(b"old")

    original_run = subprocess.run

    def download(command, *, stdout, **kwargs):
        if command[0] != "gh":
            return original_run(command, stdout=stdout, **kwargs)
        assert command == ["gh", "api", "repos/owner/repo/actions/artifacts/7/zip"]
        stdout.write(zipped.getvalue())

    monkeypatch.setattr(subprocess, "run", download)
    original_restore = ci_artifacts._restore_archive

    def restore(root, payload):
        downloads = list((root / ".lake").glob("lean-ci-download-*"))
        assert len(downloads) == 1
        assert [path.name for path in downloads[0].iterdir()] == ["artifact.zip"]
        return original_restore(root, payload)

    monkeypatch.setattr(ci_artifacts, "_restore_archive", restore)
    assert ci_artifacts.download_build(repository, "owner/repo", 7)
    assert output.read_bytes() == b"compiled"
    assert not list((repository / ".lake").glob("lean-ci-download-*"))


@pytest.mark.parametrize(
    "name", [ci_artifacts.ARCHIVE_NAME, ci_artifacts.LEGACY_ARCHIVE_NAME]
)
def test_download_rejects_truncated_payload(repository: Path, monkeypatch, name):
    """Decompression must finish before streamed download replaces cached output."""
    archive = repository / name
    ci_artifacts.pack_build(repository, archive)
    zipped = io.BytesIO()
    with zipfile.ZipFile(zipped, "w") as bundle:
        bundle.writestr(name, archive.read_bytes()[:-8])
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    output.write_bytes(b"old")
    original_run = subprocess.run

    def download(command, *, stdout, **kwargs):
        if command[0] != "gh":
            return original_run(command, stdout=stdout, **kwargs)
        stdout.write(zipped.getvalue())

    monkeypatch.setattr(subprocess, "run", download)
    with pytest.raises((subprocess.SubprocessError, tarfile.TarError, EOFError)):
        ci_artifacts.download_build(repository, "owner/repo", 7)
    assert output.read_bytes() == b"old"
    assert not list((repository / ".lake").glob("lean-ci-*"))
