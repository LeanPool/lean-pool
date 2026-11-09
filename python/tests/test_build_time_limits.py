"""Tests for the per-file build-time limits enforced in CI."""

from __future__ import annotations

import hashlib
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest
import yaml

from lean_pool import build_time_limits as limits

BUNDLE = "LeanPool/MovingSofa/Certificates/Bundle004.lean"
BUNDLE_MODULE = "LeanPool.MovingSofa.Certificates.Bundle004"
LAKE_LOG = """\
2026-11-06T11:21:20.3113969Z ✔ [2837/3186] Built LeanPoolLinters (732ms)
2026-11-06T11:21:21.2162561Z ✔ [3944/5542] Built LeanPoolLinters:c.o (971ms)
✔ [8835/8879] Built LeanPool.MovingSofa.Certificates.Bundle023 (485s)
✔ [8855/8879] Built LeanPool.MovingSofa.Certificates.Bundle004 (865s)
✔ [10/20] Built LeanPool.Quick.Basic (812ms)
✔ [11/20] Built LeanPool.Quick.Basic:c.o (2.1s)
✔ [12/20] Replayed LeanPool.Quick.Cached
"""


def test_parse_elapsed_accepts_every_ps_format() -> None:
    """Elapsed times parse in every format ``ps`` prints."""
    assert limits.parse_elapsed("01:05") == 65
    assert limits.parse_elapsed("02:01:05") == 7265
    assert limits.parse_elapsed("3-02:01:05") == 3 * 86400 + 7265
    with pytest.raises(ValueError):
        limits.parse_elapsed("soon")


def test_process_table_finds_only_overdue_lean_processes_of_the_build() -> None:
    """Only the build's own Lean processes that ran too long are stopped."""
    table = limits.parse_process_table(
        """\
  100     1   100    02:00:00 /usr/bin/python3 -m lean_pool.build_time_limits watch
  101   100   100    02:00:00 /home/runner/.elan/bin/lake build LeanPool
  102   101   100    01:00:01 /home/runner/.elan/bin/v4/lean LeanPool/A/Slow.lean -o x
  103   101   100       05:00 /home/runner/.elan/bin/v4/lean LeanPool/A/Fast.lean
  104     1     1    09:00:00 /home/runner/.elan/bin/v4/lean Unrelated.lean
  105   101   100    02:00:00 /bin/sh -c leanc
  106     1   100    01:30:00 /home/runner/.elan/bin/v4/lean LeanPool/A/Orphan.lean
garbage line
"""
    )
    overdue = limits.overdue_lean_processes(table, root=100, limit=3600)
    assert sorted(process.pid for process in overdue) == [102, 106]
    assert limits.source_of(overdue[0]) == "LeanPool/A/Slow.lean"


def test_unreadable_process_table_is_an_error(monkeypatch) -> None:
    """A failing ``ps`` is reported, never read as an empty table."""

    def failing(*_arguments, **_options):
        return subprocess.CompletedProcess(["ps"], 1, stdout="", stderr="denied")

    monkeypatch.setattr(limits.subprocess, "run", failing)
    with pytest.raises(limits.ProcessTableError):
        limits.read_process_table()


def test_module_times_reads_pool_modules_only() -> None:
    """Build times come from pool modules, not facets or other libraries."""
    times = limits.module_times(LAKE_LOG)
    assert times == {
        "LeanPool.MovingSofa.Certificates.Bundle023": 485.0,
        "LeanPool.MovingSofa.Certificates.Bundle004": 865.0,
        "LeanPool.Quick.Basic": 0.812,
    }


def test_violations_cover_changed_files_only(
    tmp_path: Path, monkeypatch, capsys
) -> None:
    """Duration violations stay separate from strict missing-timing rejection."""
    times = limits.module_times(LAKE_LOG)
    changed = {
        BUNDLE_MODULE: BUNDLE,
        "LeanPool.Quick.Basic": "LeanPool/Quick/Basic.lean",
        "LeanPool.Quick.Cached": "LeanPool/Quick/Cached.lean",
    }
    found = limits.violations(times, changed, limit=600)
    assert found == [limits.Violation(BUNDLE, 865.0)]
    log = tmp_path / "build.log"
    log.write_text(LAKE_LOG)
    monkeypatch.setattr(limits, "changed_modules", lambda base, root: changed)
    # At900s no observed module is too slow; Cached still lacks a fresh timing.
    assert limits.check(log, "base", tmp_path, limit=900) == 1
    output = capsys.readouterr().out
    assert "No fresh successful build timing for LeanPool/Quick/Cached.lean" in output


def _git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(["git", *arguments], cwd=root, text=True).strip()


def _repository(tmp_path: Path) -> tuple[Path, str]:
    root = tmp_path / "repository"
    (root / "LeanPool" / "MovingSofa" / "Certificates").mkdir(parents=True)
    _git(root.parent, "init", "-q", str(root))
    _git(root, "config", "user.email", "ci@example.com")
    _git(root, "config", "user.name", "CI")
    bundle = root / "LeanPool" / "MovingSofa" / "Certificates" / "Bundle023.lean"
    bundle.write_text("-- old\n")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "base")
    base = _git(root, "rev-parse", "HEAD")
    (root / "LeanPool" / "MovingSofa" / "Certificates" / "Bundle004.lean").write_text(
        ""
    )
    (root / "notes.lean").write_text("")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "head")
    return root, base


def test_check_fails_on_slow_added_file(tmp_path: Path, capsys) -> None:
    """An added file over the limit fails with an annotation."""
    root, base = _repository(tmp_path)
    log = tmp_path / "build.log"
    log.write_text(LAKE_LOG)
    assert limits.changed_modules(base, root) == {BUNDLE_MODULE: BUNDLE}
    assert limits.check(log, base, root, limit=600) == 1
    output = capsys.readouterr().out
    assert "::error file=LeanPool/MovingSofa/Certificates/Bundle004.lean::" in output
    assert "865 s" in output


def test_check_ignores_slow_unchanged_files(tmp_path: Path) -> None:
    """A slow file the PR did not touch passes while changed files are fast."""
    root, base = _repository(tmp_path)
    log = tmp_path / "build.log"
    log.write_text(
        "✔ [1/2] Built LeanPool.MovingSofa.Certificates.Bundle023 (900s)\n"
        f"✔ [2/2] Built {BUNDLE_MODULE} (300s)\n"
    )
    assert limits.check(log, base, root, limit=600) == 0


def _fake_lean(tmp_path: Path, body: str) -> tuple[Path, Path]:
    """A Python script run through a symlink named ``lean``."""
    lean = tmp_path / "lean"
    lean.symlink_to(sys.executable)
    script = tmp_path / "work.py"
    script.write_text(body)
    return lean, script


def _alive(pid: int) -> bool:
    """A killed orphan awaiting its adopter is no longer a running writer."""
    return limits._process_state(pid) not in {None, "Z", "X"}


def test_watch_stops_a_lean_process_past_the_limit(tmp_path: Path) -> None:
    """A Lean process past the hard limit is stopped and the build fails."""
    fake_lean = tmp_path / "lean"
    fake_lean.symlink_to(shutil.which("sleep") or "/bin/sleep")
    build = ["/bin/sh", "-c", f"'{fake_lean}' 60; exit 0"]
    started = time.monotonic()
    assert limits.watch(build, limit=1, poll=0.2, grace=0.5) == 124
    assert time.monotonic() - started < 30


def test_watch_kills_a_stop_ignoring_lean_after_its_parent_exits(
    tmp_path: Path,
) -> None:
    """A Lean process that ignores TERM and outlives its parent is still killed."""
    pid_file = tmp_path / "pid"
    lean, script = _fake_lean(
        tmp_path,
        "import os, signal, sys, time\n"
        "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
        f"open({str(pid_file)!r}, 'w').write(str(os.getpid()))\n"
        "while True:\n"
        "    print('still writing', flush=True)\n"
        "    time.sleep(0.1)\n",
    )
    build = ["/bin/sh", "-c", f"'{lean}' '{script}' > /dev/null & sleep 2; exit 0"]
    started = time.monotonic()
    assert limits.watch(build, limit=1, poll=0.2, grace=0.5) == 124
    assert time.monotonic() - started < 30
    pid = int(pid_file.read_text())
    deadline = time.monotonic() + 5
    while _alive(pid) and time.monotonic() < deadline:
        time.sleep(0.1)
    assert not _alive(pid)


def test_watch_leaves_no_owned_process_behind(tmp_path: Path) -> None:
    """Background processes the build leaves running are stopped on return."""
    pid_file = tmp_path / "pid"
    build = ["/bin/sh", "-c", f"sleep 60 & echo $! > '{pid_file}'; exit 0"]
    assert limits.watch(build, limit=60, poll=0.2, grace=0.5) == 0
    pid = int(pid_file.read_text())
    deadline = time.monotonic() + 5
    while _alive(pid) and time.monotonic() < deadline:
        time.sleep(0.1)
    assert not _alive(pid)


def test_watch_stops_the_build_when_ps_fails(monkeypatch) -> None:
    """Without a readable process table the build is stopped, not left unwatched."""

    def unreadable() -> list[limits.Process]:
        raise limits.ProcessTableError("ps exited with status 1")

    monkeypatch.setattr(limits, "read_process_table", unreadable)
    started = time.monotonic()
    build = [sys.executable, "-c", "import time; time.sleep(60)"]
    assert limits.watch(build, limit=60, poll=0.2, grace=0.5) == 125
    assert time.monotonic() - started < 30


def test_watch_passes_through_the_build_status() -> None:
    """Without a stopped process the build exit status is kept."""
    assert limits.watch([sys.executable, "-c", "raise SystemExit(3)"], limit=60) == 3
    assert limits.watch([sys.executable, "-c", "pass"], limit=60) == 0


def _outputs(root: Path, module: str) -> list[Path]:
    relative = Path(*module.split("."))
    folder = root / ".lake/build/lib/lean" / relative.parent
    folder.mkdir(parents=True, exist_ok=True)
    files = [folder / f"{relative.name}.{suffix}" for suffix in ("olean", "trace")]
    for file in files:
        file.write_text("compiled\n")
    return files


def test_prepare_rebuilds_changed_files_from_a_pre_policy_cache(
    tmp_path: Path,
) -> None:
    """A restored build without the policy marker recompiles changed files."""
    root, base = _repository(tmp_path)
    changed = _outputs(root, BUNDLE_MODULE)
    unchanged = _outputs(root, "LeanPool.MovingSofa.Certificates.Bundle023")
    assert limits.prepare(base, root) == 0
    assert not any(file.exists() for file in changed)
    assert all(file.exists() for file in unchanged)


def test_prepare_rebuilds_even_with_a_matching_legacy_policy_marker(
    tmp_path: Path,
) -> None:
    """A global marker cannot certify a changed file on a later source reversion."""
    root, base = _repository(tmp_path)
    changed = _outputs(root, BUNDLE_MODULE)
    log = tmp_path / "build.log"
    log.write_text(f"✔ [1/1] Built {BUNDLE_MODULE} (300s)\n")
    assert limits.check(log, base, root, limit=600) == 0
    marker = root / ".lake/build/lean-pool-build-time-policy"
    marker.write_text(hashlib.sha256(Path(limits.__file__).read_bytes()).hexdigest())
    assert limits.prepare(base, root) == 0
    assert not any(file.exists() for file in changed)


def test_failed_check_does_not_mark_the_build(tmp_path: Path) -> None:
    """A build with an over-limit file is never marked as passing."""
    root, base = _repository(tmp_path)
    _outputs(root, BUNDLE_MODULE)
    log = tmp_path / "build.log"
    log.write_text(LAKE_LOG)
    assert limits.check(log, base, root, limit=600) == 1
    assert not (root / ".lake/build/lean-pool-build-time-policy").exists()


def test_read_process_table_fails_on_observer_error(monkeypatch) -> None:
    """A failed observer cannot masquerade as an empty successful observation."""
    run = subprocess.run

    def failed_observer(command, **kwargs):
        assert command[0] == "ps"
        return run([sys.executable, "-c", "raise SystemExit(2)"], **kwargs)

    monkeypatch.setattr(limits.subprocess, "run", failed_observer)
    with pytest.raises(limits.ProcessTableError):
        limits.read_process_table()


def _resistant_build(
    tmp_path: Path,
    *,
    exit_immediately: bool = False,
    exit_status: int = 7,
    escape_session: bool = False,
) -> list[str]:
    """Create a Lean-named output writer that survives its parent's TERM."""
    lean = tmp_path / "lean"
    lean.symlink_to(sys.executable)
    marker = tmp_path / "parent-exit"
    child_script = (
        "import os,pathlib,signal,time\n"
        f"marker=pathlib.Path({str(marker)!r})\n"
        "signal.signal(signal.SIGTERM, lambda *_: marker.write_text('TERM'))\n"
        f"pathlib.Path({str(tmp_path / 'child.pid')!r}).write_text(str(os.getpid()))\n"
        "print('OWNED_CHILD_PID='+str(os.getpid()),flush=True)\n"
        "time.sleep(60)\n"
    )
    script = (
        "import pathlib,signal,subprocess,sys,time\n"
        "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))\n"
        f"child=subprocess.Popen([{str(lean)!r},'-c',{child_script!r}], "
        "preexec_fn=lambda:signal.signal(signal.SIGTERM,signal.SIG_IGN),"
        f"start_new_session={escape_session!r})\n"
        f"while not pathlib.Path({str(tmp_path / 'child.pid')!r})"
        ".exists():time.sleep(0.01)\n"
        + (
            f"raise SystemExit({exit_status})\n"
            if exit_immediately
            else f"while not pathlib.Path({str(marker)!r}).exists():time.sleep(0.01)\n"
        )
    )
    return [sys.executable, "-c", script]


def _assert_not_running(pid: int) -> None:
    """A killed orphan may await its adopter's reap, but cannot retain a writer."""
    process = next((p for p in limits.read_process_table() if p.pid == pid), None)
    assert process is None or limits._process_state(process.pid) in {None, "Z", "X"}


@pytest.mark.parametrize("escape_session", [False, True])
def test_watch_kills_resistant_writer_after_parent_exit(
    tmp_path: Path, escape_session: bool
) -> None:
    """TERM must not release a still-open output pipe before owned KILL cleanup."""
    build = _resistant_build(tmp_path, escape_session=escape_session)
    runner = (
        "from lean_pool import build_time_limits as limits\n"
        "limits.TERMINATE_GRACE_SECONDS=0.2\n"
        f"status=limits.watch({build!r},limit=0,poll=0.02,grace=0.2)\n"
        "print('WATCH_RETURN='+str(status),flush=True)\n"
    )
    unrelated = subprocess.Popen(
        [str(tmp_path / "lean"), "-c", "import time;time.sleep(60)"]
    )
    watcher = subprocess.Popen(
        [sys.executable, "-c", runner],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        output, error = watcher.communicate(timeout=10)
        assert watcher.returncode == 0, error
        assert "WATCH_RETURN=124" in output
        assert "::error file=" in output
        _assert_not_running(int((tmp_path / "child.pid").read_text()))
        assert unrelated.poll() is None
    finally:
        unrelated.kill()
        unrelated.wait()
        if watcher.poll() is None:
            watcher.kill()
            watcher.wait()
        if (tmp_path / "child.pid").exists():
            try:
                os.kill(int((tmp_path / "child.pid").read_text()), signal.SIGKILL)
            except ProcessLookupError:
                pass


def test_watch_cleans_orphan_on_normal_parent_exit(tmp_path: Path, monkeypatch) -> None:
    """An already-exited leader keeps its status while its orphan is cleaned."""
    monkeypatch.setattr(limits, "TERMINATE_GRACE_SECONDS", 0.2)
    assert (
        limits.watch(
            _resistant_build(tmp_path, exit_immediately=True), 60, 0.02, grace=0.2
        )
        == 7
    )
    _assert_not_running(int((tmp_path / "child.pid").read_text()))


def test_watch_observer_failure_cleans_owned_group(tmp_path: Path, monkeypatch) -> None:
    """Failure after the writer starts still kills it and reports failure."""
    read_table = limits.read_process_table
    failed = False

    def failing_observer():
        nonlocal failed
        failed = failed or (tmp_path / "child.pid").exists()
        if failed:
            raise subprocess.CalledProcessError(2, ["ps"])
        return read_table()

    monkeypatch.setattr(limits, "TERMINATE_GRACE_SECONDS", 0.2)
    monkeypatch.setattr(limits, "read_process_table", failing_observer)
    assert limits.watch(_resistant_build(tmp_path), 60, 0.02, grace=0.2) == 125
    monkeypatch.setattr(limits, "read_process_table", read_table)
    deadline = time.monotonic() + 2
    pid = int((tmp_path / "child.pid").read_text())
    while time.monotonic() < deadline:
        process = next((p for p in read_table() if p.pid == pid), None)
        if process is None or limits._process_state(process.pid) in {None, "Z", "X"}:
            break
        time.sleep(0.01)
    _assert_not_running(pid)


def test_cleanup_observer_failure_cannot_return_success(tmp_path: Path, monkeypatch):
    """Even a successful leader exit cannot hide cleanup-only observer failure."""
    read_table = limits.read_process_table
    finish_group = limits._finish_group
    cleaning = False

    def failing_during_cleanup():
        if cleaning:
            raise subprocess.CalledProcessError(2, ["ps"])
        return read_table()

    def cleanup(*args):
        nonlocal cleaning
        cleaning = True
        return finish_group(*args)

    monkeypatch.setattr(limits, "TERMINATE_GRACE_SECONDS", 0.2)
    monkeypatch.setattr(limits, "read_process_table", failing_during_cleanup)
    monkeypatch.setattr(limits, "_finish_group", cleanup)
    build = _resistant_build(tmp_path, exit_immediately=True, exit_status=0)
    assert limits.watch(build, 60, 0.02, grace=0.2) == 125
    monkeypatch.setattr(limits, "read_process_table", read_table)
    _assert_not_running(int((tmp_path / "child.pid").read_text()))


def test_watch_prunes_exited_process_handles(monkeypatch):
    """Sequential compiler-sized processes do not accumulate ownership handles."""
    open_pidfd, close = limits.os.pidfd_open, limits.os.close
    active: set[int] = set()
    peak = opened = 0

    def track_open(pid):
        nonlocal peak, opened
        descriptor = open_pidfd(pid)
        active.add(descriptor)
        opened += 1
        peak = max(peak, len(active))
        return descriptor

    def track_close(descriptor):
        active.discard(descriptor)
        return close(descriptor)

    monkeypatch.setattr(limits.os, "pidfd_open", track_open)
    monkeypatch.setattr(limits.os, "close", track_close)
    script = (
        "import subprocess,sys\n"
        "for _ in range(40):\n"
        " subprocess.run([sys.executable,'-c','import time;time.sleep(0.02)'],"
        "check=True)\n"
    )
    assert limits.watch([sys.executable, "-c", script], 60, 0.005) == 0
    assert opened > 10
    assert peak <= 3
    assert not active


def test_stale_process_row_does_not_adopt_unrelated_pid(monkeypatch):
    """A recycled PID must prove a current owned relation, not stale ps ancestry."""
    unrelated = subprocess.Popen([sys.executable, "-c", "import time;time.sleep(60)"])
    opened: list[int] = []
    open_pidfd = limits.os.pidfd_open

    def track_open(pid):
        descriptor = open_pidfd(pid)
        opened.append(descriptor)
        return descriptor

    monkeypatch.setattr(limits.os, "pidfd_open", track_open)
    owned = {}
    try:
        stale = limits.Process(unrelated.pid, 99999999, 99999999, 3601, "lean")
        assert not limits._remember(stale, 99999999, owned)
        assert not owned
        assert unrelated.poll() is None
        for descriptor in opened:
            with pytest.raises(OSError):
                os.fstat(descriptor)
    finally:
        unrelated.kill()
        unrelated.wait()


def test_first_snapshot_traverses_nested_escaped_writer(tmp_path: Path, monkeypatch):
    """A same-group intermediary cannot hide an escaped grandchild at parent exit."""
    intermediary = _resistant_build(tmp_path, escape_session=True)
    leader_pid = tmp_path / "leader.pid"
    script = (
        "import os,pathlib,subprocess,time\n"
        f"pathlib.Path({str(leader_pid)!r}).write_text(str(os.getpid()))\n"
        f"subprocess.Popen({intermediary!r})\n"
        f"while not pathlib.Path({str(tmp_path / 'child.pid')!r})"
        ".exists():time.sleep(0.01)\n"
    )
    read_table = limits.read_process_table
    first = True

    def snapshot_after_leader_exit():
        nonlocal first
        if not first:
            return read_table()
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            table = read_table()
            if leader_pid.exists():
                pid = int(leader_pid.read_text())
                if any(
                    p.pid == pid and limits._process_state(p.pid) in {"Z", "X"}
                    for p in table
                ):
                    first = False
                    return read_table()
            time.sleep(0.01)
        raise AssertionError("test build leader did not exit")

    monkeypatch.setattr(limits, "TERMINATE_GRACE_SECONDS", 0.2)
    monkeypatch.setattr(limits, "read_process_table", snapshot_after_leader_exit)
    assert limits.watch([sys.executable, "-c", script], 60, 0.02, grace=0.2) == 0
    monkeypatch.setattr(limits, "read_process_table", read_table)
    _assert_not_running(int((tmp_path / "child.pid").read_text()))


def _artifact(root: Path, module: str, suffix: str, directory="lib/lean") -> Path:
    path = root / ".lake/build" / directory / (module.replace(".", "/") + suffix)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("cached compiled artifact\n")
    return path


def test_prepare_removes_all_changed_artifact_variants_only(tmp_path: Path):
    """Oleans, private/server siblings, traces and IR cannot resurrect old timings."""
    root, base = _repository(tmp_path)
    changed = [
        _artifact(root, BUNDLE_MODULE, suffix)
        for suffix in (
            ".olean",
            ".olean.private",
            ".olean.server",
            ".olean.hash",
            ".ilean",
            ".trace",
        )
    ]
    changed += [
        _artifact(root, BUNDLE_MODULE, suffix, "ir")
        for suffix in (".c", ".c.o", ".bc", ".trace")
    ]
    untouched = _artifact(root, "LeanPool.MovingSofa.Certificates.Bundle023", ".olean")
    prefix_neighbor = _artifact(root, BUNDLE_MODULE + "Other", ".olean")
    source = (root / BUNDLE).read_bytes()
    assert limits.prepare(base, root) == 0
    assert all(not path.exists() for path in changed)
    assert (
        untouched.read_text()
        == prefix_neighbor.read_text()
        == "cached compiled artifact\n"
    )
    assert (root / BUNDLE).read_bytes() == source


@pytest.mark.parametrize("log_text", ["", f"Replayed {BUNDLE_MODULE}\n"])
def test_check_rejects_missing_or_replayed_changed_file_timing(
    tmp_path: Path, capsys, log_text: str
):
    """A changed file needs a successful Built timing, not merely cached output."""
    root, base = _repository(tmp_path)
    log = tmp_path / "build.log"
    log.write_text(log_text)
    assert limits.check(log, base, root, 600) == 1
    assert "No fresh successful build timing" in capsys.readouterr().out


def test_same_policy_source_revert_rebuilds_and_checks_slow_file(tmp_path: Path):
    """A retained S1 cache cannot hide an865s file when S2 is reverted to S1."""
    root, _ = _repository(tmp_path)
    first = (root / BUNDLE).read_text()
    (root / BUNDLE).write_text("-- faster S2\n")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "source two under same policy")
    base = _git(root, "rev-parse", "HEAD")
    (root / BUNDLE).write_text(first)
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "revert to source one under same policy")
    artifact = _artifact(root, BUNDLE_MODULE, ".olean")
    trace = _artifact(root, BUNDLE_MODULE, ".trace")
    assert limits.prepare(base, root) == 0
    assert not artifact.exists() and not trace.exists()
    log = tmp_path / "build.log"
    log.write_text(f"Replayed {BUNDLE_MODULE}\n")
    assert limits.check(log, base, root, 600) == 1
    log.write_text(f"Built {BUNDLE_MODULE} (865s)\n")
    assert limits.check(log, base, root, 600) == 1
    log.write_text(f"Built {BUNDLE_MODULE} (300s)\n")
    assert limits.check(log, base, root, 600) == 0


def test_prepare_and_check_scope_other_shard_and_explicit_empty(tmp_path: Path):
    """A shard checks only changed modules it builds; an empty scope checks none."""
    root, base = _repository(tmp_path)
    other_module = "LeanPool.Other.Fast"
    other = root / "LeanPool/Other/Fast.lean"
    other.parent.mkdir(parents=True)
    other.write_text("-- another changed project\n")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "another shard")
    own_artifact = _artifact(root, BUNDLE_MODULE, ".olean")
    other_artifact = _artifact(root, other_module, ".olean")
    assert limits.prepare(base, root, []) == 0
    assert own_artifact.exists() and other_artifact.exists()
    log = tmp_path / "build.log"
    log.write_text("")
    assert limits.check(log, base, root, 600, modules=[]) == 0
    assert limits.prepare(base, root, [BUNDLE_MODULE]) == 0
    assert not own_artifact.exists() and other_artifact.exists()
    log.write_text(f"Built {BUNDLE_MODULE} (300s)\n")
    assert limits.check(log, base, root, 600, modules=[BUNDLE_MODULE]) == 0
    assert limits.check(log, base, root, 600) == 1


def test_assembly_skips_projects_its_shards_already_timed(tmp_path: Path):
    """Assembly neither rebuilds nor re-times changed files a shard just checked."""
    root, base = _repository(tmp_path)
    shard_output = _artifact(root, BUNDLE_MODULE, ".olean")
    log = tmp_path / "build.log"
    log.write_text("")
    assert limits.prepare(base, root, exclude_projects=["MovingSofa"]) == 0
    assert shard_output.exists()
    assert limits.check(log, base, root, 600, exclude_projects=["MovingSofa"]) == 0
    assert limits.check(log, base, root, 600, exclude_projects=["Other"]) == 1


def test_noncontent_change_has_no_fresh_timing_requirement(tmp_path: Path):
    """A noncontent PR neither invalidates old output nor checks untouched files."""
    root, _ = _repository(tmp_path)
    base = _git(root, "rev-parse", "HEAD")
    (root / "README.md").write_text("Documentation only\n")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "noncontent change")
    artifact = _artifact(root, BUNDLE_MODULE, ".olean")
    log = tmp_path / "build.log"
    log.write_text("")
    assert limits.prepare(base, root) == 0
    assert artifact.exists()
    assert limits.check(log, base, root, 600) == 0


def test_prepare_and_check_cli_distinguish_absent_and_empty_scope(tmp_path: Path):
    """Workflow CLI empty-module arguments preserve the explicit empty shard."""
    root, base = _repository(tmp_path)
    artifact = _artifact(root, BUNDLE_MODULE, ".olean")
    log = tmp_path / "build.log"
    log.write_text("")
    common = ["--base", base, "--root", str(root)]
    assert limits.main(["prepare", *common, "--modules"]) == 0
    assert artifact.exists()
    assert limits.main(["check", *common, "--log", str(log), "--modules"]) == 0
    assert limits.main(["prepare", *common]) == 0
    assert not artifact.exists()
    assert limits.main(["check", *common, "--log", str(log)]) == 1


def test_empty_successful_process_table_is_an_error(monkeypatch) -> None:
    """A successful ps invocation still has to report usable process rows."""

    def empty(*_arguments, **_options):
        return subprocess.CompletedProcess(["ps"], 0, stdout="", stderr="")

    monkeypatch.setattr(limits.subprocess, "run", empty)
    with pytest.raises(limits.ProcessTableError):
        limits.read_process_table()


@pytest.mark.parametrize("number", [signal.SIGINT, signal.SIGTERM])
def test_watch_forwards_signals_and_restores_handlers(tmp_path: Path, number: int):
    """Cancellation reaches the owned build while normal child status is kept."""
    ready = tmp_path / "ready"
    received = tmp_path / "received"
    build = (
        "import pathlib,signal,sys,time\n"
        "def end(number,frame):\n"
        f" pathlib.Path({str(received)!r}).write_text(str(number))\n"
        " raise SystemExit(42)\n"
        "signal.signal(signal.SIGINT,end)\n"
        "signal.signal(signal.SIGTERM,end)\n"
        f"pathlib.Path({str(ready)!r}).write_text('ready')\n"
        "while True:time.sleep(0.01)\n"
    )
    runner = (
        "import signal,sys\n"
        "from lean_pool import build_time_limits as limits\n"
        "previous={n:signal.getsignal(n) for n in (signal.SIGINT,signal.SIGTERM)}\n"
        f"status=limits.watch([sys.executable,'-c',{build!r}],60,0.01,grace=0.1)\n"
        "assert all(signal.getsignal(n)==h for n,h in previous.items())\n"
        "print('WATCH_RETURN='+str(status),flush=True)\n"
    )
    watcher = subprocess.Popen(
        [sys.executable, "-c", runner],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        deadline = time.monotonic() + 5
        while not ready.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert ready.exists()
        watcher.send_signal(number)
        output, error = watcher.communicate(timeout=5)
        assert watcher.returncode == 0, error
        assert "WATCH_RETURN=42" in output
        assert received.read_text() == str(number)
    finally:
        if watcher.poll() is None:
            watcher.kill()
            watcher.wait()


def test_workflow_rebuilds_changed_modules_after_all_compiled_restores() -> None:
    """Every build mode measures its actual changed-module scope after reuse."""
    root = Path(__file__).resolve().parents[2]
    workflow = yaml.safe_load(
        (root / ".github/workflows/lean_action_ci.yml").read_text()
    )
    for name in ("build", "shard", "finalize", "rebase"):
        steps = workflow["jobs"][name]["steps"]
        indices = [
            index
            for index, step in enumerate(steps)
            if "lean_pool.build_time_limits watch" in step.get("run", "")
        ]
        assert len(indices) == 1
        index = indices[0]
        script = steps[index]["run"]
        for command in ("prepare", "watch", "check"):
            assert script.count(f"lean_pool.build_time_limits {command}") == 1
        assert script.index("build_time_limits prepare") < script.index(
            "build_time_limits watch"
        )
        assert script.index("build_time_limits watch") < script.index(
            "build_time_limits check"
        )
        assert script.count('--base "$time_base"') == 2
        assert 'git cat-file -e "$BUILD_TIME_BASE"' in script
        assert 'time_base=""' in script
        if name == "shard":
            assert (
                'git ls-files -- "LeanPool/$project.lean" "LeanPool/$project/"'
                in script
            )
            assert script.count("--modules $modules") == 2
            assert "lake build $modules" in script
        else:
            assert "--modules" not in script
            assert "lake build LeanPool" in script
        if name == "finalize":
            assert "include.*.projects" in steps[index]["env"]["SHARD_PROJECTS"]
            assert script.count("--exclude-projects $SHARD_PROJECTS") == 2
        else:
            assert "--exclude-projects" not in script
        for restore_index, step in enumerate(steps):
            run = step.get("run", "")
            cache = step.get("uses", "").startswith("actions/cache/restore@") and (
                step.get("with", {}).get("path") == ".lake/build"
            )
            compiled = any(
                command in run
                for command in (
                    "-m lean_pool.ci_pr_build",
                    "-m lean_pool.rebase_fastpath restore",
                    "-m lean_pool.ci_artifacts restore-queue",
                    "tar -x",
                )
            ) or ("-m lean_pool.queue_build" in run and "--receipts" not in run)
            if cache or compiled:
                assert restore_index < index, (name, step.get("name"))
            if "-m lean_pool.queue_build" in run and "--receipts" in run:
                assert restore_index > index
