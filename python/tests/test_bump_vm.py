"""Exercise VM checkout recovery, quota waterfalls and independent validation."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from unittest.mock import Mock

import pytest

from lean_pool import bump_vm
from lean_pool.bump_vm import Runner, rank_accounts


def account(name: str, used: float | None, **overrides: object) -> dict:
    """Describe an authenticated account without reading any credentials."""
    return {
        "name": name,
        "usedPercent": used,
        "ready": True,
        "authenticated": True,
        "identityOk": True,
        "available": True,
        **overrides,
    }


def test_quota_order_prefers_remaining_usage_over_reset_time() -> None:
    """Sooner resets do not outrank more available quota."""
    statuses = [
        account("soon", 80, resetsAt=1),
        account("most", 5, resetsAt=999999),
        account("middle", 30),
    ]
    assert rank_accounts(statuses) == ["most", "middle", "soon"]


def test_unknown_exhausted_or_other_provider_accounts_are_excluded() -> None:
    """Incomplete probes, identity failures, and Claude never enter the waterfall."""
    statuses = [
        account("good", 0),
        account("unknown", None),
        account("nonfinite", float("nan")),
        account("exhausted", 98),
        account("logged-out", 1, authenticated=False),
        account("wrong-user", 1, identityOk=False),
        account("blocked", 1, available=False),
        account("claude", 0),
        account("other", 0, provider="anthropic"),
    ]
    assert rank_accounts(statuses) == ["good"]


@pytest.fixture
def runner(tmp_path: Path) -> Runner:
    """Construct an isolated controller with a pending test release."""
    (tmp_path / "logs").mkdir()
    result = Runner(tmp_path)
    result.checkpoint(target="v4.35.0")
    return result


def test_waterfall_reprobes_and_keeps_edits_after_failure(
    runner: Runner, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A failing or falsely successful agent cannot stop project verification."""
    statuses = [account("first", 0), account("second", 5), account("third", 20)]
    probes = iter([statuses, [account("second", 90), account("third", 10)]])
    attempts = []
    monkeypatch.setattr(
        runner,
        "command",
        lambda *args: json.dumps(next(probes)) if args[0] == "cx" else "revision",
    )
    monkeypatch.setattr(runner, "prompt", lambda project: "continue partial edits")
    commits = Mock()
    monkeypatch.setattr(runner, "commit_repairs", commits)
    builds = Mock(side_effect=[False, True])
    monkeypatch.setattr(runner, "build_project", builds)

    def attempt(arguments: list[str], name: str, prompt: str) -> int:
        attempts.append(arguments[:3])
        assert "--ignore-user-config" in arguments
        assert prompt == "continue partial edits"
        return 1 if len(attempts) == 1 else 0

    monkeypatch.setattr(runner, "logged", attempt)
    runner.repair("Example")
    assert attempts == [["cx", "first", "exec"], ["cx", "third", "exec"]]
    assert commits.call_count == 2
    assert runner.state["project"] is None


def test_all_accounts_failing_retains_checkpoint(
    runner: Runner, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Exhaustion waits for service retry instead of looping on the same account."""
    statuses = json.dumps([account("only", 0)])
    monkeypatch.setattr(
        runner, "command", lambda *args: statuses if args[0] == "cx" else "head"
    )
    monkeypatch.setattr(runner, "prompt", lambda project: "repair")
    monkeypatch.setattr(runner, "logged", Mock(return_value=0))
    monkeypatch.setattr(runner, "commit_repairs", Mock())
    monkeypatch.setattr(runner, "build_project", Mock(return_value=False))
    with pytest.raises(RuntimeError, match="waterfall exhausted"):
        runner.repair("Example")
    assert runner.logged.call_count == 1
    assert json.loads(runner.state_path.read_text())["project"] == "Example"


def git(root: Path, *arguments: str) -> str:
    """Run real local Git commands for ancestry and dirty-tree regressions."""
    return subprocess.check_output(["git", *arguments], cwd=root, text=True).strip()


def test_shallow_checkout_resumes_real_branch_with_common_ancestor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Reproduce the old unrelated-histories failure and merge both lines of work."""
    source = tmp_path / "source"
    source.mkdir()
    git(source, "init", "-b", "main")
    git(source, "config", "user.name", "Test")
    git(source, "config", "user.email", "test@example.com")
    (source / "base").write_text("base")
    git(source, "add", ".")
    git(source, "commit", "-m", "base")
    git(source, "checkout", "-b", "bump/v4.35.0")
    (source / "repair").write_text("existing repair")
    git(source, "add", ".")
    git(source, "commit", "-m", "existing repair")
    repair = git(source, "rev-parse", "HEAD")
    git(source, "checkout", "main")
    (source / "upstream").write_text("new main work")
    git(source, "add", ".")
    git(source, "commit", "-m", "main moved")
    upstream = git(source, "rev-parse", "HEAD")
    remote = tmp_path / "remote.git"
    git(tmp_path, "clone", "--bare", str(source), str(remote))
    monkeypatch.setattr(bump_vm, "REMOTE", remote.as_uri())
    root = tmp_path / "runtime"
    root.mkdir()
    git(
        root, "clone", "--depth", "1", "--branch", "main", remote.as_uri(), "repository"
    )
    worker = Runner(root)
    worker.checkpoint(target="v4.35.0")
    assert git(worker.repository, "rev-parse", "--is-shallow-repository") == "true"
    worker.checkout()
    monkeypatch.setattr(worker, "update_pins", Mock())
    original = worker.command
    monkeypatch.setattr(
        worker,
        "command",
        lambda *args, **kw: "" if args[0] == "lake" else original(*args, **kw),
    )
    worker.prepare_branch("v4.35.0")
    assert git(worker.repository, "rev-parse", "--is-shallow-repository") == "false"
    git(worker.repository, "merge-base", "--is-ancestor", repair, "HEAD")
    git(worker.repository, "merge-base", "--is-ancestor", upstream, "HEAD")


@pytest.mark.parametrize(
    "path", [".github/workflows/check.yml", "LeanPool/Other/File.lean"]
)
def test_out_of_scope_repairs_are_preserved_but_never_committed(
    runner: Runner, monkeypatch: pytest.MonkeyPatch, path: str
) -> None:
    """A checkpoint cannot silently include unrelated agent edits."""
    monkeypatch.setattr(runner, "changed_paths", lambda: [path])
    commands = Mock()
    monkeypatch.setattr(runner, "command", commands)
    with pytest.raises(RuntimeError, match="unexpected path"):
        runner.commit_repairs("Example")
    commands.assert_not_called()


def test_build_success_with_warnings_still_needs_repair(
    runner: Runner, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Warnings remain a gate even when Lake returns zero."""
    (runner.root / "logs" / "build-Example.log").write_text(
        "warning: unused simp argument"
    )
    monkeypatch.setattr(runner, "logged", Mock(return_value=0))
    assert not runner.build_project("Example")


def test_all_existing_gates_run_and_failure_is_retained(
    runner: Runner, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The agent's exit status never substitutes for build and quality gates."""
    (runner.root / "logs" / "whole-pool.log").write_text("Build completed successfully")
    calls = []

    def logged(arguments: list[str], name: str) -> int:
        calls.append(name)
        return int(name == "gate-quality.log")

    monkeypatch.setattr(runner, "logged", logged)
    results = runner.validate()
    assert results == dict(
        build=True, indexes=True, linter=True, style=True, quality=False
    )
    assert len(calls) == 5
    assert runner.state_path.exists()


def test_pin_update_is_recovered_before_checkout_fetch(
    runner: Runner, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An interruption between rewriting pins and refreshing manifests is resumable."""
    runner.checkpoint(phase="pins")
    runner.repository.mkdir()
    calls = []

    def command(*arguments: str) -> str:
        calls.append(arguments)
        if arguments[:3] == ("git", "remote", "get-url"):
            return bump_vm.REMOTE
        return "false"

    def update() -> None:
        calls.append(("finish-pins",))

    monkeypatch.setattr(runner, "command", command)
    monkeypatch.setattr(runner, "changed_paths", lambda: [])
    monkeypatch.setattr(runner, "update_pins", update)
    runner.checkout()
    finish = calls.index(("finish-pins",))
    fetch = next(i for i, call in enumerate(calls) if call[:2] == ("git", "fetch"))
    assert finish < fetch
