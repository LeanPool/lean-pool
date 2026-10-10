"""Regression checks for interrupted weekly profiling and dataset publication."""

import importlib.util
import json
import subprocess
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[2] / "scripts/weekly-profile/run.py"
SPECIFICATION = importlib.util.spec_from_file_location("weekly_profile", SCRIPT)
weekly_profile = importlib.util.module_from_spec(SPECIFICATION)
SPECIFICATION.loader.exec_module(weekly_profile)


def test_failed_capture_keeps_pinned_state_and_cannot_publish(monkeypatch, tmp_path):
    """Retries preserve completed preparation and never publish partial captures."""
    state = {
        "runId": "test-run",
        "commit": "pool-commit",
        "profilerCommit": "profiler-commit",
        "phase": "prepare",
    }
    commands = []

    def command(*arguments, directory, capture=False):
        commands.append(arguments)
        if arguments[0] == "node":
            raise subprocess.CalledProcessError(1, arguments)
        return ""

    monkeypatch.setattr(weekly_profile, "command", command)
    with pytest.raises(subprocess.CalledProcessError):
        weekly_profile.execute(tmp_path, state)
    checkpoint = json.loads((tmp_path / "active.json").read_text())
    assert checkpoint["phase"] == "capture"
    assert checkpoint["commit"] == "pool-commit"
    commands.clear()
    with pytest.raises(subprocess.CalledProcessError):
        weekly_profile.execute(tmp_path, checkpoint)
    assert len(commands) == 1
    assert commands[0][0] == "node"


def test_publication_requires_audit_for_the_pinned_commit(tmp_path):
    """A passing audit for another source revision cannot replace the snapshot."""
    export = tmp_path / "export"
    export.mkdir()
    (export / "coverage.json").write_text('{"result":"PASS"}')
    (export / "manifest.json").write_text('{"commit":"other-commit"}')
    with pytest.raises(RuntimeError, match="pinned commit"):
        weekly_profile.publish(tmp_path, {"commit": "expected-commit"})


def test_replace_dataset_preserves_viewer_and_removes_obsolete_assets(tmp_path):
    """Weekly publication must retain UI changes and remove stale file IDs."""
    export, destination = tmp_path / "export", tmp_path / "destination"
    for directory in (export / "data", destination / "data"):
        directory.mkdir(parents=True)
    (export / "data/new.json.gz").write_bytes(b"new")
    (destination / "data/old.json.gz").write_bytes(b"old")
    (destination / "app.js").write_text("current viewer")
    (destination / "index.html").write_text("current toolbar")
    (destination / "projects.yml").write_text("old registry")
    weekly_profile.replace_generated(export, destination)
    assert (destination / "app.js").read_text() == "current viewer"
    assert (destination / "index.html").read_text() == "current toolbar"
    assert (destination / "data/new.json.gz").read_bytes() == b"new"
    assert not (destination / "data/old.json.gz").exists()
    assert not (destination / "projects.yml").exists()


def test_resume_refuses_changed_private_checkout(monkeypatch, tmp_path):
    """An interrupted run cannot silently move its profiling baseline."""
    state = {
        "runId": "test-run",
        "commit": "pinned-pool-commit",
        "profilerCommit": "pinned-profiler-commit",
        "phase": "capture",
    }
    (tmp_path / "active.json").write_text(json.dumps(state))
    monkeypatch.setattr(weekly_profile, "command", lambda *args, **kwargs: "new-commit")
    with pytest.raises(RuntimeError, match="pinned repository"):
        weekly_profile.run_state(tmp_path)


def test_publication_retries_racing_push_and_retains_new_viewer(monkeypatch, tmp_path):
    """Publish a dataset against a real Git remote with a concurrent UI change."""
    remote, initial, run = tmp_path / "remote", tmp_path / "initial", tmp_path / "run"
    monkeypatch.setenv("GIT_AUTHOR_NAME", "Profile Test")
    monkeypatch.setenv("GIT_AUTHOR_EMAIL", "profile@example.invalid")
    monkeypatch.setenv("GIT_COMMITTER_NAME", "Profile Test")
    monkeypatch.setenv("GIT_COMMITTER_EMAIL", "profile@example.invalid")
    original = weekly_profile.command
    original(
        "git",
        "init",
        "--bare",
        "--initial-branch=main",
        str(remote),
        directory=tmp_path,
    )
    original("git", "clone", str(remote), str(initial), directory=tmp_path)
    pool = initial / "docs/pool"
    pool.mkdir(parents=True)
    (pool / "manifest.json").write_text('{"completedAt":"2026-10-01T00:00:00Z"}')
    (pool / "app.js").write_text("old viewer")
    original("git", "add", ".", directory=initial)
    original("git", "commit", "-m", "initial", directory=initial)
    original("git", "push", "origin", "main", directory=initial)
    export = run / "export"
    export.mkdir(parents=True)
    (export / "coverage.json").write_text('{"result":"PASS"}')
    manifest = {"commit": "pool-commit", "completedAt": "2026-10-10T00:00:00Z"}
    (export / "manifest.json").write_text(json.dumps(manifest))
    monkeypatch.setattr(weekly_profile, "PROFILER_URL", str(remote))
    raced = False

    def command(*arguments, directory, capture=False):
        nonlocal raced
        if arguments[:2] == ("git", "push") and not raced:
            raced = True
            (pool / "app.js").write_text("concurrent viewer update")
            original("git", "add", ".", directory=initial)
            original("git", "commit", "-m", "viewer update", directory=initial)
            original("git", "push", "origin", "main", directory=initial)
        return original(*arguments, directory=directory, capture=capture)

    monkeypatch.setattr(weekly_profile, "command", command)
    state = {"commit": "pool-commit"}
    publication = weekly_profile.publish(run, state)
    assert raced
    original("git", "pull", "--ff-only", directory=initial)
    assert (pool / "app.js").read_text() == "concurrent viewer update"
    assert json.loads((pool / "manifest.json").read_text()) == manifest
    assert weekly_profile.publish(run, state) == publication


def test_retention_preserves_unfinished_runs_and_two_completed_runs(tmp_path):
    """Long failed recordings must survive bounded successful-run cleanup."""
    for name in ("01", "02", "03", "unfinished"):
        run = tmp_path / "runs" / name
        run.mkdir(parents=True)
        if name != "unfinished":
            (run / "complete.json").write_text("{}")
    weekly_profile.prune_recordings(tmp_path)
    assert sorted(path.name for path in (tmp_path / "runs").iterdir()) == [
        "02",
        "03",
        "unfinished",
    ]


@pytest.fixture
def completion_run(tmp_path):
    """Prepare pinned state and retained recordings for finalization recovery."""
    state = {
        "runId": "03-test-run",
        "commit": "pinned-pool-commit",
        "profilerCommit": "pinned-profiler-commit",
        "phase": "prepare",
    }
    run = tmp_path / "runs" / state["runId"]
    run.mkdir(parents=True)
    (tmp_path / "pending").touch()
    for name in ("01", "02", "unfinished"):
        previous = tmp_path / "runs" / name
        previous.mkdir()
        if name != "unfinished":
            (previous / "complete.json").write_text("{}")
    weekly_profile.write_json(tmp_path / "active.json", state)
    return {"root": tmp_path, "state": state, "run": run}


@pytest.fixture
def completion_operations(monkeypatch, completion_run):
    """Record mocked commands and publications without invoking external work."""
    root = completion_run["root"]
    state = completion_run["state"]
    run = completion_run["run"]
    commands, publications = [], []
    monkeypatch.setenv("LAKE", "test-lake")

    def command(*arguments, directory, capture=False):
        commands.append(arguments)
        if arguments[:3] == ("git", "rev-parse", "HEAD"):
            assert capture
            assert directory in (root / "repository", root / "profiler")
            return {
                "repository": state["commit"],
                "profiler": state["profilerCommit"],
            }[directory.name]
        assert not capture
        name = "repository" if arguments[0] == "test-lake" else "profiler"
        assert directory == root / name
        return ""

    def publish(recording, checkpoint):
        assert recording == run
        assert checkpoint["runId"] == state["runId"]
        assert checkpoint["commit"] == "pinned-pool-commit"
        assert checkpoint["profilerCommit"] == "pinned-profiler-commit"
        assert checkpoint["phase"] == "publish"
        publications.append(dict(checkpoint))
        return "publication-commit"

    monkeypatch.setattr(weekly_profile, "command", command)
    monkeypatch.setattr(weekly_profile, "publish", publish)
    return commands, publications


@pytest.fixture
def completion_marker_failure(monkeypatch, completion_run):
    """Install a single failure before or after atomic marker publication."""
    write_json = weekly_profile.write_json
    marker = completion_run["run"] / "complete.json"
    interrupted = False

    def install(marker_persisted):
        def interrupted_write(path, value):
            nonlocal interrupted
            if path == marker and not interrupted:
                interrupted = True
                if marker_persisted:
                    write_json(path, value)
                raise OSError("interrupted completion marker write")
            write_json(path, value)

        monkeypatch.setattr(weekly_profile, "write_json", interrupted_write)

    return install


def assert_interrupted_completion(completion_run, marker_persisted):
    """Keep the same pinned publish checkpoint until finalization can finish."""
    root, state = completion_run["root"], completion_run["state"]
    marker = completion_run["run"] / "complete.json"
    checkpoint = json.loads((root / "active.json").read_text())
    assert checkpoint["phase"] == state["phase"] == "publish"
    assert checkpoint["runId"] == state["runId"]
    assert checkpoint["commit"] == "pinned-pool-commit"
    assert checkpoint["profilerCommit"] == "pinned-profiler-commit"
    assert marker.exists() is marker_persisted
    if marker_persisted:
        assert json.loads(marker.read_text()) == {
            **checkpoint,
            "phase": "complete",
            "publicationCommit": "publication-commit",
        }
    assert (root / "pending").exists()
    assert (root / "runs/01").exists()
    return checkpoint


def assert_completed_profile_commands(completion_run, commands):
    """Prepare, capture and export exactly once before the publish-only retry."""
    root, run = completion_run["root"], completion_run["run"]
    assert commands == [
        ("npm", "ci", "--cache", str(root / "npm-cache")),
        ("npm", "run", "build"),
        ("test-lake", "exe", "cache", "get"),
        (
            "node",
            "scripts/capture-whole-pool.cjs",
            str(root / "repository"),
            str(run / "recording"),
        ),
        (
            "python3",
            "scripts/export-whole-pool.py",
            str(run / "recording"),
            str(run / "export"),
        ),
    ]


def assert_completed_recording(completion_run, checkpoint, publications):
    """Finish both checkpoints, remove pending and retain exactly two runs."""
    root, run = completion_run["root"], completion_run["run"]
    assert len(publications) == 2
    complete = json.loads((run / "complete.json").read_text())
    assert complete == json.loads((root / "active.json").read_text())
    assert complete == {
        **checkpoint,
        "phase": "complete",
        "publicationCommit": "publication-commit",
    }
    assert not (root / "pending").exists()
    assert sorted(path.name for path in (root / "runs").iterdir()) == [
        "02",
        "03-test-run",
        "unfinished",
    ]


@pytest.mark.parametrize("marker_persisted", [False, True])
def test_completion_marker_failure_resumes_same_run(
    completion_run, completion_operations, completion_marker_failure, marker_persisted
):
    """A finalization interruption must not strand a captured recording."""
    root, state = completion_run["root"], completion_run["state"]
    commands, publications = completion_operations
    completion_marker_failure(marker_persisted)
    with pytest.raises(OSError, match="completion marker"):
        weekly_profile.execute(root, state)
    checkpoint = assert_interrupted_completion(completion_run, marker_persisted)
    completed_commands = list(commands)
    assert_completed_profile_commands(completion_run, completed_commands)

    resumed = weekly_profile.run_state(root)
    assert resumed == checkpoint
    weekly_profile.execute(root, resumed)
    assert commands[:5] == completed_commands
    assert commands[5:] == [
        ("git", "rev-parse", "HEAD"),
        ("git", "rev-parse", "HEAD"),
    ]
    assert_completed_recording(completion_run, checkpoint, publications)
