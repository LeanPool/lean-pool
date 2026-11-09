"""Tests for the per-file build-time limits enforced in CI."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import pytest

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


def test_violations_cover_changed_files_only() -> None:
    """Only changed files that were compiled and ran long are reported."""
    times = limits.module_times(LAKE_LOG)
    changed = {
        BUNDLE_MODULE: BUNDLE,
        "LeanPool.Quick.Basic": "LeanPool/Quick/Basic.lean",
        "LeanPool.Quick.Cached": "LeanPool/Quick/Cached.lean",
    }
    found = limits.violations(times, changed, limit=600)
    assert found == [limits.Violation(BUNDLE, 865.0)]


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
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


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


def test_prepare_keeps_a_build_that_passed_this_policy(tmp_path: Path) -> None:
    """A passing check marks the build, so its outputs are reused next time."""
    root, base = _repository(tmp_path)
    changed = _outputs(root, BUNDLE_MODULE)
    log = tmp_path / "build.log"
    log.write_text(f"✔ [1/1] Built {BUNDLE_MODULE} (300s)\n")
    assert limits.check(log, base, root, limit=600) == 0
    assert (root / limits.POLICY_MARKER).read_text().strip() == limits.policy_digest()
    assert limits.prepare(base, root) == 0
    assert all(file.exists() for file in changed)


def test_failed_check_does_not_mark_the_build(tmp_path: Path) -> None:
    """A build with an over-limit file is never marked as passing."""
    root, base = _repository(tmp_path)
    _outputs(root, BUNDLE_MODULE)
    log = tmp_path / "build.log"
    log.write_text(LAKE_LOG)
    assert limits.check(log, base, root, limit=600) == 1
    assert not (root / limits.POLICY_MARKER).exists()
