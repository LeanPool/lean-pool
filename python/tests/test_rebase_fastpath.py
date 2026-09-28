"""The rebase shortcut must reject edits that need a fresh full validation."""

from __future__ import annotations

import io
import json
import subprocess
import tarfile
import zipfile
from pathlib import Path

import pytest

from lean_pool import rebase_fastpath


def _git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(["git", *arguments], cwd=root, text=True).strip()


def _run(root: Path, *arguments: str) -> None:
    subprocess.run(["git", *arguments], cwd=root, check=True, capture_output=True)


def _index(root: Path) -> None:
    modules = sorted(path.stem for path in (root / "LeanPool").glob("*.lean"))
    (root / "LeanPool.lean").write_text(
        "module  -- shake: keep-all --deprecated_module: ignore\n\n"
        + "".join(f"public import LeanPool.{name}\n" for name in modules)
    )


def _commit(root: Path, message: str) -> str:
    _run(root, "add", ".")
    _run(root, "commit", "-qm", message)
    return _git(root, "rev-parse", "HEAD")


@pytest.fixture
def rebased(tmp_path: Path) -> tuple[Path, str, str, str, str]:
    """Construct a passing PR followed by a mechanical content merge of main."""
    root = tmp_path / "repo"
    root.mkdir()
    _run(root, "init", "-q", "-b", "main")
    _run(root, "config", "user.email", "test@example.com")
    _run(root, "config", "user.name", "Test")
    (root / "LeanPool").mkdir()
    (root / "LeanPool/A.lean").write_text("module\n")
    (root / "LeanPool/projects.yml").write_text("projects:\n  - slug: a\n")
    for name in rebase_fastpath.PINNED_INPUTS:
        (root / name).write_text(name)
    _index(root)
    old_base = _commit(root, "base")

    _run(root, "checkout", "-qb", "pr")
    (root / "LeanPool/B.lean").write_text("module\npublic import LeanPool.A\n")
    (root / "LeanPool/projects.yml").write_text("projects:\n  - slug: a\n  - slug: b\n")
    _index(root)
    previous = _commit(root, "add B")

    _run(root, "checkout", "-q", "main")
    (root / "LeanPool/C.lean").write_text("module\npublic import LeanPool.A\n")
    (root / "LeanPool/projects.yml").write_text("projects:\n  - slug: a\n  - slug: c\n")
    _index(root)
    base = _commit(root, "add C")

    _run(root, "checkout", "-q", "pr")
    subprocess.run(
        ["git", "merge", "--no-ff", "--no-commit", "main"],
        cwd=root,
        capture_output=True,
    )
    (root / "LeanPool/projects.yml").write_text(
        "projects:\n  - slug: a\n  - slug: c\n  - slug: b\n"
    )
    _index(root)
    head = _commit(root, "merge main")
    return root, old_base, previous, base, head


def _github(
    monkeypatch: pytest.MonkeyPatch, previous: str, *, green: bool = True
) -> None:
    def read(endpoint: str) -> dict:
        if endpoint.endswith("/artifacts?per_page=100"):
            return {
                "artifacts": [
                    {"id": 8, "name": rebase_fastpath.ARTIFACT, "expired": False}
                ]
            }
        return {
            "workflow_runs": [
                {
                    "id": 7,
                    "head_sha": previous,
                    "conclusion": "success" if green else "failure",
                    # GitHub may report the PR's current base on an old run.
                    "pull_requests": [{"number": 42, "base": {"sha": "f" * 40}}],
                }
            ]
        }

    monkeypatch.setattr(rebase_fastpath, "github_json", read)


def test_green_content_rebase_uses_fast_path(
    rebased: tuple[Path, str, str, str, str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """A green PR and unchanged owned module can reuse its compiled project."""
    root, _, previous, base, head = rebased
    _github(monkeypatch, previous)
    result = rebase_fastpath.decision(
        root, "owner/repo", "lean_action_ci.yml", 42, head, base
    )
    assert result == {
        "eligible": True,
        "reason": "verified rebase",
        "run_id": 7,
        "previous_head": previous,
    }
    assert rebase_fastpath.check_index(root)
    (root / "LeanPool.lean").write_text("module\n")
    assert not rebase_fastpath.check_index(root)


def test_missing_green_run_or_artifact_falls_back(
    rebased: tuple[Path, str, str, str, str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """Unverified or expired evidence never bypasses Lean compilation."""
    root, _, previous, base, head = rebased
    _github(monkeypatch, previous, green=False)
    assert not rebase_fastpath.decision(
        root, "owner/repo", "lean_action_ci.yml", 42, head, base
    )["eligible"]
    _github(monkeypatch, previous)
    monkeypatch.setattr(rebase_fastpath, "_has_build_artifact", lambda *_: False)
    assert not rebase_fastpath.decision(
        root, "owner/repo", "lean_action_ci.yml", 42, head, base
    )["eligible"]
    assert rebase_fastpath.decision(root, "owner/repo", "docs.yml", 42, head, base)[
        "eligible"
    ]


def test_merged_pr_run_can_have_no_pull_request_association(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """GitHub removes PR associations from old runs after their PR merges."""
    head = "a" * 40
    monkeypatch.setattr(
        rebase_fastpath,
        "github_json",
        lambda _: {
            "workflow_runs": [
                {
                    "id": 7,
                    "head_sha": head,
                    "conclusion": "success",
                    "pull_requests": [],
                }
            ]
        },
    )
    assert (
        rebase_fastpath._successful_run("owner/repo", "lean_action_ci.yml", 42, head)
        is None
    )
    assert rebase_fastpath._successful_run(
        "owner/repo", "lean_action_ci.yml", 42, head, merged=True
    ) == {"id": 7, "head_sha": head, "conclusion": "success", "pull_requests": []}


def test_changed_pr_project_rejected(
    rebased: tuple[Path, str, str, str, str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """Edits to the PR's own proof require ordinary CI."""
    root, _, previous, base, _ = rebased
    _github(monkeypatch, previous)
    _run(root, "reset", "--hard", "HEAD^")
    subprocess.run(
        ["git", "merge", "--no-ff", "--no-commit", "main"],
        cwd=root,
        capture_output=True,
    )
    (root / "LeanPool/B.lean").write_text("module\npublic import LeanPool.C\n")
    (root / "LeanPool/projects.yml").write_text(
        "projects:\n  - slug: a\n  - slug: c\n  - slug: b\n"
    )
    _index(root)
    head = _commit(root, "merge and edit B")
    assert not rebase_fastpath.decision(
        root, "owner/repo", "lean_action_ci.yml", 42, head, base
    )["eligible"]


def test_main_build_input_change_rejected(
    rebased: tuple[Path, str, str, str, str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """A toolchain change must invalidate earlier results."""
    root, _, previous, _, _ = rebased
    _github(monkeypatch, previous)
    _run(root, "reset", "--hard", previous)
    _run(root, "checkout", "-q", "main")
    (root / "lean-toolchain").write_text("different toolchain")
    base = _commit(root, "bump toolchain")
    _run(root, "checkout", "-q", "pr")
    subprocess.run(
        ["git", "merge", "--no-ff", "--no-commit", "main"],
        cwd=root,
        capture_output=True,
    )
    (root / "LeanPool/projects.yml").write_text(
        "projects:\n  - slug: a\n  - slug: c\n  - slug: b\n"
    )
    _index(root)
    head = _commit(root, "merge new main")
    result = rebase_fastpath.decision(
        root, "owner/repo", "lean_action_ci.yml", 42, head, base
    )
    assert result["reason"] == "main changed shared build or validation inputs"


def test_main_edit_to_existing_lean_source_rejected(
    rebased: tuple[Path, str, str, str, str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """A changed dependency may invalidate a previous proof or axiom audit."""
    root, _, previous, _, _ = rebased
    _github(monkeypatch, previous)
    _run(root, "reset", "--hard", previous)
    _run(root, "checkout", "-q", "main")
    (root / "LeanPool/A.lean").write_text("module\n-- changed dependency\n")
    base = _commit(root, "modify A")
    _run(root, "checkout", "-q", "pr")
    subprocess.run(
        ["git", "merge", "--no-ff", "--no-commit", "main"],
        cwd=root,
        capture_output=True,
    )
    (root / "LeanPool/projects.yml").write_text(
        "projects:\n  - slug: a\n  - slug: c\n  - slug: b\n"
    )
    _index(root)
    head = _commit(root, "merge changed A")
    result = rebase_fastpath.decision(
        root, "owner/repo", "lean_action_ci.yml", 42, head, base
    )
    assert result["reason"] == "main edited existing Lean sources"


def test_changed_project_card_rejected(
    rebased: tuple[Path, str, str, str, str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """A bot merge cannot silently alter the PR's validated project card."""
    root, _, previous, base, _ = rebased
    _github(monkeypatch, previous)
    _run(root, "reset", "--hard", previous)
    subprocess.run(
        ["git", "merge", "--no-ff", "--no-commit", "main"],
        cwd=root,
        capture_output=True,
    )
    (root / "LeanPool/projects.yml").write_text(
        "projects:\n  - slug: a\n  - slug: c\n  - slug: b-edited\n"
    )
    _index(root)
    head = _commit(root, "merge with changed card")
    result = rebase_fastpath.decision(root, "owner/repo", "docs.yml", 42, head, base)
    assert result["reason"] == "project cards changed beyond the merge"


def test_project_archive_contains_only_pr_module(
    rebased: tuple[Path, str, str, str, str], tmp_path: Path
) -> None:
    """The reusable artifact excludes the rest of the large pool build."""
    root, _, _, base, head = rebased
    for project in ("A", "B", "C"):
        path = root / ".lake/build/lib/lean/LeanPool" / f"{project}.olean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(project)
    archive_path = tmp_path / "build.tar.gz"
    rebase_fastpath.pack(root, base, head, archive_path)
    with tarfile.open(archive_path, "r:gz") as archive:
        names = archive.getnames()
        manifest = json.load(archive.extractfile(rebase_fastpath.MANIFEST))
    assert manifest["projects"] == ["B"]
    assert ".lake/build/lib/lean/LeanPool/B.olean" in names
    assert ".lake/build/lib/lean/LeanPool/A.olean" not in names
    assert ".lake/build/lib/lean/LeanPool/C.olean" not in names


def test_restore_checks_sources_before_overlay(
    rebased: tuple[Path, str, str, str, str],
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A changed project cannot consume an old olean artifact."""
    root, old_base, previous, _, _ = rebased
    compiled = root / ".lake/build/lib/lean/LeanPool/B.olean"
    compiled.parent.mkdir(parents=True)
    compiled.write_text("validated build")
    archive_path = tmp_path / "build.tar.gz"
    rebase_fastpath.pack(root, old_base, previous, archive_path)
    compiled.unlink()
    wrapper = io.BytesIO()
    with zipfile.ZipFile(wrapper, "w") as zipped:
        zipped.writestr(rebase_fastpath.ARCHIVE, archive_path.read_bytes())

    monkeypatch.setattr(
        rebase_fastpath,
        "github_json",
        lambda _: {
            "artifacts": [{"id": 8, "name": rebase_fastpath.ARTIFACT, "expired": False}]
        },
    )

    def download(
        command: list[str], *, stdout: io.BufferedWriter, **_kwargs: object
    ) -> None:
        assert command == ["gh", "api", "repos/owner/repo/actions/artifacts/8/zip"]
        stdout.write(wrapper.getvalue())

    monkeypatch.setattr(rebase_fastpath.subprocess, "run", download)
    source = root / "LeanPool/B.lean"
    original = source.read_text()
    source.write_text("module\n-- unvalidated edit\n")
    with pytest.raises(ValueError, match="project build inputs changed"):
        rebase_fastpath.restore(root, "owner/repo", 7, previous)
    assert not compiled.exists()
    source.write_text(original)
    rebase_fastpath.restore(root, "owner/repo", 7, previous)
    assert compiled.read_text() == "validated build"


def test_new_main_project_reuses_its_merged_pr_artifact(
    rebased: tuple[Path, str, str, str, str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """The main-cache gap need not force every waiting PR to compile the merger."""
    root, _, previous, base, _ = rebased
    merged_head = "c" * 40
    restored = []

    def read(endpoint: str) -> list[dict]:
        assert endpoint == f"repos/owner/repo/commits/{base}/pulls"
        return [{"number": 99, "head": {"sha": merged_head}, "merged_at": "now"}]

    monkeypatch.setattr(rebase_fastpath, "github_json", read)
    monkeypatch.setattr(rebase_fastpath, "_successful_run", lambda *_, **__: {"id": 11})
    monkeypatch.setattr(rebase_fastpath, "_has_build_artifact", lambda *_: True)
    monkeypatch.setattr(
        rebase_fastpath,
        "restore",
        lambda *args: restored.append(args),
    )
    rebase_fastpath.restore_new_main_projects(root, "owner/repo", previous, base)
    assert restored == [(root, "owner/repo", 11, merged_head)]
