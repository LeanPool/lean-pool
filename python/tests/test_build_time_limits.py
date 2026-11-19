"""Tests for the per-file build-time limits enforced in CI."""

from __future__ import annotations

import hashlib
import json
import os
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
    monkeypatch.setattr(limits, "added_files", lambda base, root: frozenset())
    # At900s no observed module is too slow; Cached still lacks a fresh timing.
    assert limits.check(log, "base", tmp_path, limit=900) == 1
    output = capsys.readouterr().out
    assert "No successful build timing for LeanPool/Quick/Cached.lean" in output


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
    # Not a symlink to `sleep`: a multicall coreutils binary (uutils) invoked
    # as `lean` exits at once instead of sleeping.
    fake_lean, script = _fake_lean(tmp_path, "import time\ntime.sleep(60)\n")
    build = ["/bin/sh", "-c", f"'{fake_lean}' '{script}'; exit 0"]
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
    build = [
        "/bin/sh",
        "-c",
        f"trap 'exit 0' TERM; '{lean}' '{script}' > /dev/null & wait",
    ]
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


MEBIBYTE = 1024**2
# Holds its memory until it is killed; touching every page makes it resident.
HOLD_MEMORY = "import time\nblock = b'x' * (200 * 1024**2)\ntime.sleep(60)\n"
# Holds the same memory for a moment and then finishes its file.
HOLD_AND_FINISH = (
    "import sys, time\nblock = b'x' * (200 * 1024**2)\ntime.sleep(1.5)\n"
    "open(sys.argv[1] + '.built', 'w').write('built')\n"
)


def _sources(tmp_path: Path, *names: str) -> list[Path]:
    sources = [tmp_path / "LeanPool" / name for name in names]
    for source in sources:
        source.parent.mkdir(parents=True, exist_ok=True)
    return sources


def _limits(tmp_path: Path, *added: str, floor: int = 0) -> limits.MemoryLimits:
    return limits.MemoryLimits(
        added_file=64 * MEBIBYTE,
        added=frozenset(f"LeanPool/{name}" for name in added),
        root=tmp_path,
        floor=floor,
    )


def test_process_memory_counts_anonymous_memory_only() -> None:
    """Held memory is counted; a process that is gone reports none."""
    holder = subprocess.Popen([sys.executable, "-c", HOLD_MEMORY])
    try:
        deadline = time.monotonic() + 10
        used = 0
        while used < 200 * MEBIBYTE and time.monotonic() < deadline:
            used = limits.process_memory(holder.pid) or 0
            time.sleep(0.05)
        assert 200 * MEBIBYTE <= used < 400 * MEBIBYTE
    finally:
        holder.kill()
        holder.wait()
    assert limits.process_memory(holder.pid) is None


def test_an_added_file_over_its_memory_limit_is_stopped(tmp_path: Path, capfd) -> None:
    """The added file is named and stopped; an existing file of that size builds."""
    lean, script = _fake_lean(tmp_path, HOLD_AND_FINISH)
    added, existing = _sources(tmp_path, "New/Added.lean", "Old/Existing.lean")
    build = [
        "/bin/sh",
        "-c",
        f"'{lean}' '{script}' '{added}' & '{lean}' '{script}' '{existing}'; wait",
    ]
    started = time.monotonic()
    status = limits.watch(
        build, limit=60, poll=0.1, grace=0.5, memory=_limits(tmp_path, "New/Added.lean")
    )
    assert status == limits.MEMORY_STATUS
    assert time.monotonic() - started < 30
    assert not Path(f"{added}.built").exists()
    assert Path(f"{existing}.built").read_text() == "built"
    output = capfd.readouterr().out
    assert output.count("::error file=LeanPool/New/Added.lean::") == 1
    assert "limit for a file a pull request adds is 0.1 GiB" in output
    assert "::error file=LeanPool/Old/Existing.lean" not in output
    assert "for each of the 1 files this change adds" in output.splitlines()[0]


def test_memory_stop_decides_the_status_even_when_the_build_fails(
    tmp_path: Path,
) -> None:
    """Lake exits 1 after a killed file; the status still says why."""
    lean, script = _fake_lean(tmp_path, HOLD_MEMORY)
    (added,) = _sources(tmp_path, "New/Added.lean")
    build = ["/bin/sh", "-c", f"'{lean}' '{script}' '{added}'; exit 1"]
    memory = _limits(tmp_path, "New/Added.lean")
    assert limits.watch(build, limit=60, poll=0.1, grace=0.5, memory=memory) == 123


def test_large_processes_that_are_not_lean_are_left_alone(
    tmp_path: Path, monkeypatch
) -> None:
    """The limits are for compiling files, not for Lake or the linters."""
    monkeypatch.setattr(limits, "free_memory", lambda: 0)
    script = tmp_path / "work.py"
    script.write_text("block = b'x' * (200 * 1024**2)\nimport time\ntime.sleep(1)\n")
    memory = _limits(tmp_path, floor=1024**3)
    assert limits.watch([sys.executable, str(script)], 60, poll=0.1, memory=memory) == 0


def test_the_largest_compiler_is_stopped_when_the_machine_runs_out(
    tmp_path: Path, monkeypatch, capfd
) -> None:
    """A runner that is about to die names what was compiling and stops one file."""
    # Like Lake, the build fails when one of its compilers was killed.
    lean, large = _fake_lean(tmp_path, HOLD_MEMORY)
    small = tmp_path / "small.py"
    small.write_text(
        "import sys, time\ntime.sleep(2)\n"
        "open(sys.argv[1] + '.built', 'w').write('b')\n"
    )
    heavy, light = _sources(tmp_path, "A/Heavy.lean", "B/Light.lean")
    stopped = []

    def free() -> int:
        # Out of memory until one compiler has been stopped.
        return 4 * 1024**3 if stopped else 100 * MEBIBYTE

    kill = limits.MemoryWatch._kill

    def record(self, identity):
        stopped.append(identity.pid)
        return kill(self, identity)

    monkeypatch.setattr(limits, "free_memory", free)
    monkeypatch.setattr(limits.MemoryWatch, "_kill", record)
    build = [
        "/bin/sh",
        "-c",
        f"'{lean}' '{large}' '{heavy}' & first=$!; sleep 0.5; "
        f"'{lean}' '{small}' '{light}'; wait $first",
    ]
    memory = _limits(tmp_path, floor=1024**3)
    status = limits.watch(build, limit=60, poll=0.1, grace=0.5, memory=memory)
    assert status == limits.MEMORY_STATUS
    assert len(stopped) == 1
    assert Path(f"{light}.built").read_text() == "b"
    errors = [line for line in capfd.readouterr().out.splitlines() if "::error" in line]
    assert len(errors) == 1
    assert errors[0].startswith(
        "::error file=LeanPool/A/Heavy.lean::The machine had 0.1 GiB"
    )
    assert "LeanPool/A/Heavy.lean held the most and was stopped" in errors[0]


def test_nothing_is_stopped_while_the_machine_has_memory(
    tmp_path: Path, monkeypatch
) -> None:
    """An existing file may hold any amount the machine can spare."""
    monkeypatch.setattr(limits, "free_memory", lambda: 8 * 1024**3)
    lean, script = _fake_lean(tmp_path, HOLD_AND_FINISH)
    (existing,) = _sources(tmp_path, "Old/Existing.lean")
    build = ["/bin/sh", "-c", f"'{lean}' '{script}' '{existing}'"]
    memory = _limits(tmp_path, floor=1024**3)
    assert limits.watch(build, limit=60, poll=0.1, memory=memory) == 0
    assert Path(f"{existing}.built").read_text() == "built"


def _processes(monkeypatch, table: dict[int, tuple[int, str, int]]) -> list[int]:
    """Replace the live process readers by a table: number -> birth, file, bytes."""
    signals: list[int] = []
    monkeypatch.setattr(
        limits,
        "command_line",
        lambda pid: ["/toolchain/bin/lean", table[pid][1]] if pid in table else None,
    )
    monkeypatch.setattr(
        limits, "process_memory", lambda pid: table[pid][2] if pid in table else None
    )
    monkeypatch.setattr(
        limits, "_birth", lambda pid: table[pid][0] if pid in table else None
    )
    monkeypatch.setattr(limits, "_running", lambda identity: True)
    monkeypatch.setattr(
        limits.signal,
        "pidfd_send_signal",
        lambda descriptor, number: signals.append(descriptor),
    )
    return signals


def test_relief_waits_until_a_stopped_compiler_is_gone(monkeypatch, capsys) -> None:
    """One shortage stops one file, not every file seen before memory returns."""
    table = {
        41: (1000, "LeanPool/First.lean", 6 * 1024**3),
        42: (1001, "LeanPool/Second.lean", 5 * 1024**3),
    }
    owned = {
        41: limits.OwnedProcess(41, 1000, 7),
        42: limits.OwnedProcess(42, 1001, 8),
    }
    signals = _processes(monkeypatch, table)
    running = {7: True, 8: True}
    monkeypatch.setattr(limits, "free_memory", lambda: 200 * MEBIBYTE)
    monkeypatch.setattr(
        limits, "_running", lambda identity: running[identity.descriptor]
    )
    watch = limits.MemoryWatch(limits.MemoryLimits())
    for _ in range(3):
        watch.check(owned)
    assert signals == [7]
    running[7] = False
    del owned[41], table[41]
    watch.check(owned)
    assert signals == [7, 8]
    assert [source for source, _ in watch.relief] == [
        "LeanPool/First.lean",
        "LeanPool/Second.lean",
    ]
    output = capsys.readouterr().out
    assert "LeanPool/First.lean 6.0 GiB, LeanPool/Second.lean 5.0 GiB" in output
    assert "Asked to stop LeanPool/First.lean, which held the most." in output
    assert "::error" not in output
    assert watch.peaks == {
        "LeanPool/First.lean": 6 * 1024**3,
        "LeanPool/Second.lean": 5 * 1024**3,
    }


def test_relief_is_not_held_back_by_a_reused_descriptor(monkeypatch) -> None:
    """A killed compiler's closed handle number can belong to the next compiler."""
    table = {41: (1000, "LeanPool/First.lean", 6 * 1024**3)}
    signals = _processes(monkeypatch, table)
    monkeypatch.setattr(limits, "free_memory", lambda: 200 * MEBIBYTE)
    # Every handle reports a live process, as a reused descriptor would.
    monkeypatch.setattr(limits, "_running", lambda identity: True)
    watch = limits.MemoryWatch(limits.MemoryLimits())
    watch.check({41: limits.OwnedProcess(41, 1000, 7)})
    assert signals == [7]
    # The first compiler is gone and pruned; a new one received descriptor 7.
    table.clear()
    table[43] = (2000, "LeanPool/Later.lean", 6 * 1024**3)
    watch.check({43: limits.OwnedProcess(43, 2000, 7)})
    assert signals == [7, 7]
    assert watch.stopped == {(41, 1000), (43, 2000)}
    # A recycled process number with another birth is not the stopped process.
    table.clear()
    table[41] = (3000, "LeanPool/Recycled.lean", 6 * 1024**3)
    watch.check({41: limits.OwnedProcess(41, 3000, 9)})
    assert signals == [7, 7, 9]


def test_a_compiler_that_already_ended_fails_nothing(monkeypatch, capsys) -> None:
    """Under a shortage, a candidate that exits before the signal was not stopped."""
    table = {41: (1000, "LeanPool/Gone.lean", 6 * 1024**3)}
    _processes(monkeypatch, table)
    monkeypatch.setattr(limits, "free_memory", lambda: 200 * MEBIBYTE)

    def gone(descriptor, number):
        raise ProcessLookupError

    monkeypatch.setattr(limits.signal, "pidfd_send_signal", gone)
    watch = limits.MemoryWatch(limits.MemoryLimits())
    watch.check({41: limits.OwnedProcess(41, 1000, 7)})
    assert watch.relief == [] and watch.stopped == set()
    # A compiler whose handle already reports its end is not even signalled.
    asked = []
    monkeypatch.setattr(limits, "_running", lambda identity: False)
    monkeypatch.setattr(
        limits.signal, "pidfd_send_signal", lambda *arguments: asked.append(arguments)
    )
    watch.check({41: limits.OwnedProcess(41, 1000, 7)})
    assert asked == [] and watch.relief == []
    assert watch.outcome(0) is None
    assert capsys.readouterr().out == ""


def test_a_stop_request_fails_only_a_build_that_fails(monkeypatch, capsys) -> None:
    """A finished compiler accepts the signal until it is reaped; Lake knows better."""
    table = {41: (1000, "LeanPool/Heavy.lean", 6 * 1024**3)}
    signals = _processes(monkeypatch, table)
    monkeypatch.setattr(limits, "free_memory", lambda: 200 * MEBIBYTE)
    watch = limits.MemoryWatch(limits.MemoryLimits())
    watch.check({41: limits.OwnedProcess(41, 1000, 7)})
    assert signals == [7]
    assert "Asked to stop LeanPool/Heavy.lean" in capsys.readouterr().out
    # Lake succeeded: the compiler had finished, and nothing was stopped.
    assert watch.outcome(0) is None
    assert capsys.readouterr().out == ""
    # Lake failed: the stop took effect, and the error names the file.
    assert watch.outcome(1) == limits.MEMORY_STATUS
    output = capsys.readouterr().out
    assert output.startswith(
        "::error file=LeanPool/Heavy.lean::The machine had 0.2 GiB"
    )
    assert "LeanPool/Heavy.lean held the most and was stopped" in output


def test_a_signal_that_stops_nothing_leaves_the_build_passing(
    tmp_path: Path, monkeypatch, capfd
) -> None:
    """End to end: a shortage, a signal the kernel discards, and a build that passes."""
    monkeypatch.setattr(limits, "free_memory", lambda: 100 * MEBIBYTE)
    monkeypatch.setattr(limits.signal, "pidfd_send_signal", lambda *arguments: None)
    lean, script = _fake_lean(tmp_path, HOLD_AND_FINISH)
    (source,) = _sources(tmp_path, "Old/Existing.lean")
    build = ["/bin/sh", "-c", f"'{lean}' '{script}' '{source}'"]
    memory = _limits(tmp_path, floor=1024**3)
    assert limits.watch(build, limit=60, poll=0.1, grace=0.5, memory=memory) == 0
    assert Path(f"{source}.built").read_text() == "built"
    output = capfd.readouterr().out
    assert "Asked to stop LeanPool/Old/Existing.lean" in output
    assert "::error" not in output


def test_an_added_file_seen_over_its_budget_fails_even_if_it_ends(
    monkeypatch, capsys
) -> None:
    """The budget is on what the file held, not on whether the signal landed."""
    table = {41: (1000, "LeanPool/New/Added.lean", 4 * 1024**3)}
    _processes(monkeypatch, table)
    monkeypatch.setattr(limits, "free_memory", lambda: 64 * 1024**3)

    def gone(descriptor, number):
        raise ProcessLookupError

    monkeypatch.setattr(limits.signal, "pidfd_send_signal", gone)
    memory = limits.MemoryLimits(added=frozenset({"LeanPool/New/Added.lean"}))
    watch = limits.MemoryWatch(memory)
    for _ in range(2):
        watch.check({41: limits.OwnedProcess(41, 1000, 7)})
    assert watch.over_budget and watch.relief == []
    assert capsys.readouterr().out.count("LeanPool/New/Added.lean held 4.0 GiB") == 1
    # Fatal even if Lake reports success.
    assert watch.outcome(0) == limits.MEMORY_STATUS


def test_a_sample_counts_only_for_the_process_whose_handle_is_held(
    monkeypatch, capsys
) -> None:
    """A reused process number must not lend its memory to another file's budget."""
    # Number 41 now belongs to a process born later than the one we hold.
    table = {41: (2000, "LeanPool/New/Added.lean", 4 * 1024**3)}
    signals = _processes(monkeypatch, table)
    monkeypatch.setattr(limits, "free_memory", lambda: 100 * MEBIBYTE)
    memory = limits.MemoryLimits(added=frozenset({"LeanPool/New/Added.lean"}))
    watch = limits.MemoryWatch(memory)
    watch.check({41: limits.OwnedProcess(41, 1000, 7)})
    assert signals == []
    assert not watch.over_budget and watch.relief == []
    assert watch.peaks == {}
    assert capsys.readouterr().out == ""
    # Lake and the shell are read from the process itself too, and never judged.
    monkeypatch.setattr(limits, "command_line", lambda pid: ["/toolchain/bin/lake"])
    watch.check({41: limits.OwnedProcess(41, 2000, 7)})
    assert signals == [] and watch.peaks == {}


def test_watch_takes_the_added_files_from_the_base(tmp_path: Path, capfd) -> None:
    """``watch --base`` budgets the files the diff adds, not those it modifies."""
    root, base = _repository(tmp_path)
    modified = root / "LeanPool" / "MovingSofa" / "Certificates" / "Bundle023.lean"
    modified.write_text("-- modified\n")
    _git(root, "commit", "-qam", "modify")
    assert limits.added_files(base, root) == frozenset({BUNDLE})
    assert BUNDLE_MODULE in limits.changed_modules(base, root)
    assert "LeanPool.MovingSofa.Certificates.Bundle023" in limits.changed_modules(
        base, root
    )
    arguments = ["watch", "--base", base, "--root", str(root), "--", "/bin/true"]
    assert limits.main(arguments) == 0
    first = capfd.readouterr().out.splitlines()[0]
    assert "3.0 GiB of memory for each of the 1 files this change adds" in first
    assert limits.watch(["/bin/true"], limit=60) == 0
    assert "each of the 0 files" in capfd.readouterr().out


def test_sources_are_matched_however_lake_names_them(tmp_path: Path) -> None:
    """Lake passes absolute paths; the diff names files relative to the root."""
    memory = limits.MemoryLimits(root=tmp_path)
    assert memory.relative(f"{tmp_path}/LeanPool/A/B.lean") == "LeanPool/A/B.lean"
    assert memory.relative("LeanPool/A/B.lean") == "LeanPool/A/B.lean"
    assert memory.relative("/elsewhere/C.lean") == "/elsewhere/C.lean"
    spaced = ["/x/bin/lean", "/repo/Lean Pool/A.lean", "-o", "out.olean"]
    assert limits.lean_source(spaced) == "/repo/Lean Pool/A.lean"
    assert limits.lean_source(["/x/bin/lake", "build", "A.lean"]) is None
    assert "python" in limits.command_line(os.getpid())[0]
    assert limits.command_line(2**22 + 12345) is None


def test_a_restored_added_file_needs_proof_of_the_memory_limit(tmp_path: Path) -> None:
    """An output restored from an earlier run is never seen by this run's watchdog."""
    root, base = _repository(tmp_path)
    assert limits.added_files(base, root) == frozenset({BUNDLE})
    for artifact in _outputs(root, BUNDLE_MODULE):
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(b"compiled")
    stem = limits._output_stem(root, BUNDLE)
    receipt = stem.with_name(stem.name + limits.RECEIPT_SUFFIX)
    digest = limits.output_digest(root, BUNDLE)
    cap = limits.ADDED_FILE_MEMORY_LIMIT_BYTES

    def write(**fields) -> None:
        receipt.write_text(json.dumps({"seconds": 5, "outputs": digest, **fields}))

    # A receipt from before the limit existed.
    write(version=1)
    assert limits.recorded_seconds(root, BUNDLE, added=True) is None
    # Timed by the current code, but as a modified file: no memory evidence.
    write(version=limits.RECEIPT_VERSION)
    assert limits.recorded_seconds(root, BUNDLE, added=False) == 5
    assert limits.recorded_seconds(root, BUNDLE, added=True) is None
    # Compiled under a looser cap than today's, or with a malformed one.
    for bad in (cap + 1, 0, True, "3 GiB"):
        write(version=limits.RECEIPT_VERSION, memory_limit=bad)
        assert limits.recorded_seconds(root, BUNDLE, added=True) is None, bad
    write(version=limits.RECEIPT_VERSION, memory_limit=cap)
    assert limits.recorded_seconds(root, BUNDLE, added=True) == 5
    # ``prepare`` keeps that output and removes one without the evidence.
    assert limits.prepare(base, root) == 0
    assert limits.output_digest(root, BUNDLE) == digest
    write(version=limits.RECEIPT_VERSION)
    assert limits.prepare(base, root) == 0
    assert limits.output_digest(root, BUNDLE) is None


def test_check_rejects_a_restored_added_file_without_the_evidence(
    tmp_path: Path, capsys
) -> None:
    """Even if ``prepare`` did not run, an unseen added file cannot pass ``check``."""
    root, base = _repository(tmp_path)
    for artifact in _outputs(root, BUNDLE_MODULE):
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(b"compiled")
    stem = limits._output_stem(root, BUNDLE)
    receipt = {
        "version": limits.RECEIPT_VERSION,
        "seconds": 5,
        "outputs": limits.output_digest(root, BUNDLE),
    }
    stem.with_name(stem.name + limits.RECEIPT_SUFFIX).write_text(json.dumps(receipt))
    log = tmp_path / "build.log"
    log.write_text("")
    assert limits.check(log, base, root, limit=600) == 1
    assert f"No successful build timing for {BUNDLE}" in capsys.readouterr().out
    receipt["memory_limit"] = limits.ADDED_FILE_MEMORY_LIMIT_BYTES
    stem.with_name(stem.name + limits.RECEIPT_SUFFIX).write_text(json.dumps(receipt))
    assert limits.check(log, base, root, limit=600) == 0


def test_check_records_the_memory_limit_for_added_files_only(tmp_path: Path) -> None:
    """Only a job that compiled the file under its watchdog writes the evidence."""
    root, base = _repository(tmp_path)
    modified = "LeanPool/MovingSofa/Certificates/Bundle023.lean"
    (root / modified).write_text("-- modified\n")
    _git(root, "commit", "-qam", "modify")
    for module in (BUNDLE_MODULE, "LeanPool.MovingSofa.Certificates.Bundle023"):
        for artifact in _outputs(root, module):
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_bytes(module.encode())
    log = tmp_path / "build.log"
    log.write_text(
        "✔ [1/2] Built LeanPool.MovingSofa.Certificates.Bundle004 (12s)\n"
        "✔ [2/2] Built LeanPool.MovingSofa.Certificates.Bundle023 (34s)\n"
    )
    assert limits.check(log, base, root, limit=600) == 0

    def receipt(path: str) -> dict:
        stem = limits._output_stem(root, path)
        return json.loads(stem.with_name(stem.name + limits.RECEIPT_SUFFIX).read_text())

    assert receipt(BUNDLE)["memory_limit"] == limits.ADDED_FILE_MEMORY_LIMIT_BYTES
    assert "memory_limit" not in receipt(modified)
    assert receipt(BUNDLE)["version"] == limits.RECEIPT_VERSION == 2
    # A later run restores both outputs and accepts both without compiling.
    assert limits.prepare(base, root) == 0
    assert limits.output_digest(root, BUNDLE) is not None
    assert limits.output_digest(root, modified) is not None


def test_heavy_files_are_listed_after_the_build(capsys) -> None:
    """A file near its limit is visible in the log before it crosses it."""
    watch = limits.MemoryWatch(limits.MemoryLimits())
    watch.peaks = {
        "LeanPool/A/Small.lean": 1024**3,
        "LeanPool/B/Heavy.lean": 8 * 1024**3,
    }
    watch.report()
    assert capsys.readouterr().out == "Peak memory 8.0 GiB: LeanPool/B/Heavy.lean\n"


def test_the_added_file_limit_fits_four_compilers_in_a_ci_runner() -> None:
    """Lake compiles four files at once; the hosted runner reports 15.6 GiB."""
    runner_memory = int(15.6 * 1024**3)
    # Imports mapped by every compiler, Lake, this watchdog and the system.
    reserve = int(2.5 * 1024**3)
    # What a compiler can gain between two looks at its memory.
    overshoot = 200 * MEBIBYTE * limits.POLL_SECONDS
    largest = limits.ADDED_FILE_MEMORY_LIMIT_BYTES + overshoot
    assert 4 * largest + reserve <= runner_memory
    # Measured on main on 2026-11-19: every file but two held at most 2.67 GiB.
    assert limits.ADDED_FILE_MEMORY_LIMIT_BYTES >= int(1.1 * 2.67 * 1024**3)
    # The floor must outlast one interval of four compilers growing at once.
    assert limits.MEMORY_FLOOR_BYTES >= 4 * overshoot


def test_watch_records_the_limits_and_the_machine(tmp_path: Path, capfd) -> None:
    """A build log shows what the runner had, so the limits can be rechecked."""
    meminfo = tmp_path / "meminfo"
    meminfo.write_text(
        "MemTotal:       16374528 kB\nMemAvailable:    8000000 kB\n"
        "Cached: 5 kB\nSwapTotal:  4194300 kB\nSwapFree:  4194300 kB\n"
    )
    assert limits.machine_memory(meminfo) == {
        "MemTotal": 16374528 * 1024,
        "MemAvailable": 8000000 * 1024,
        "SwapTotal": 4194300 * 1024,
        "SwapFree": 4194300 * 1024,
    }
    assert limits.free_memory() > 0
    assert limits.watch([sys.executable, "-c", "pass"], limit=3600) == 0
    first = capfd.readouterr().out.splitlines()[0]
    assert first.startswith("Limits for one Lean process: 60 minutes, and 3.0 GiB")
    assert " This machine has " in first


def test_watch_ignores_an_impossible_elapsed_time(tmp_path: Path, monkeypatch) -> None:
    """Procps 4.0.4 reported a newborn process as 441,077,234 days old."""
    assert limits.parse_elapsed("441077234-00:18:40") > 3600
    lean, script = _fake_lean(tmp_path, "import time\ntime.sleep(1)\n")
    read = limits.read_process_table

    def newborn_rows() -> list[limits.Process]:
        return [
            limits.Process(
                process.pid,
                process.parent,
                process.group,
                limits.parse_elapsed("441077234-00:18:40"),
                process.arguments,
            )
            if limits.is_lean_process(process)
            else process
            for process in read()
        ]

    monkeypatch.setattr(limits, "read_process_table", newborn_rows)
    build = ["/bin/sh", "-c", f"'{lean}' '{script}' Quick.lean; exit 0"]
    assert limits.watch(build, limit=60, poll=0.1, grace=0.5) == 0


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
    deadline = time.monotonic() + 2
    while time.monotonic() < deadline:
        if limits._process_state(pid) in {None, "Z", "X"}:
            return
        time.sleep(0.01)
    pytest.fail(f"owned process {pid} is still running after cleanup")


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


def test_watch_prunes_exited_process_handles(tmp_path: Path, monkeypatch):
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
        (tmp_path / str(pid)).touch()
        return descriptor

    def track_close(descriptor):
        active.discard(descriptor)
        return close(descriptor)

    monkeypatch.setattr(limits.os, "pidfd_open", track_open)
    monkeypatch.setattr(limits.os, "close", track_close)
    child = (
        "import os,pathlib,time\n"
        f"observed=pathlib.Path({str(tmp_path)!r})/str(os.getpid())\n"
        "deadline=time.monotonic()+5\n"
        "while not observed.exists() and time.monotonic()<deadline:time.sleep(0.005)\n"
        "assert observed.exists(), 'watcher never observed child'\n"
    )
    script = (
        "import subprocess,sys\n"
        "for _ in range(40):\n"
        f" subprocess.run([sys.executable,'-c',{child!r}],check=True)\n"
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
    assert "No successful build timing" in capsys.readouterr().out


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


def _timed(root: Path, base: str, tmp_path: Path, seconds: int = 300) -> Path:
    """Compile outputs for the changed bundle and record their build time."""
    artifact = _artifact(root, BUNDLE_MODULE, ".olean")
    log = tmp_path / "timed.log"
    log.write_text(f"Built {BUNDLE_MODULE} ({seconds}s)\n")
    assert limits.check(log, base, root, 900) == 0
    return artifact


def test_recorded_time_spares_the_rebuild_of_unchanged_output(tmp_path: Path, capsys):
    """Output timed by an earlier run is kept and passes without a fresh build."""
    root, base = _repository(tmp_path)
    artifact = _timed(root, base, tmp_path)
    assert limits.recorded_seconds(root, BUNDLE) == 300.0
    assert limits.prepare(base, root) == 0
    assert artifact.exists()
    log = tmp_path / "build.log"
    log.write_text(f"Replayed {BUNDLE_MODULE}\n")
    capsys.readouterr()
    assert limits.check(log, base, root, 600) == 0
    assert "0 compiled in this job, 1 with a time recorded" in capsys.readouterr().out


def test_recorded_time_over_the_limit_still_fails(tmp_path: Path, capsys):
    """Reusing output never launders a slow file: its recorded time is checked."""
    root, base = _repository(tmp_path)
    _timed(root, base, tmp_path, seconds=865)
    log = tmp_path / "build.log"
    log.write_text("")
    assert limits.check(log, base, root, 600) == 1
    assert "took 865 s to build" in capsys.readouterr().out


@pytest.mark.parametrize("suffix", [".olean", ".olean.private", ".olean.server"])
def test_recorded_time_does_not_cover_different_output(tmp_path: Path, suffix: str):
    """A receipt certifies only the exact compiled files it was measured for."""
    root, base = _repository(tmp_path)
    artifact = _timed(root, base, tmp_path)
    _artifact(root, BUNDLE_MODULE, suffix).write_text("compiled by an untimed build\n")
    assert limits.recorded_seconds(root, BUNDLE) is None
    assert limits.prepare(base, root) == 0
    assert not artifact.exists()
    stem = artifact.with_suffix("")
    assert not stem.with_name(stem.name + limits.RECEIPT_SUFFIX).exists()
    log = tmp_path / "build.log"
    log.write_text("")
    assert limits.check(log, base, root, 600) == 1


@pytest.mark.parametrize(
    "receipt",
    [
        "{",
        "[]",
        '{"version": 0, "seconds": 1, "outputs": "DIGEST"}',
        '{"version": 2, "seconds": true, "outputs": "DIGEST"}',
        '{"version": 2, "seconds": -1, "outputs": "DIGEST"}',
        '{"version": 2, "seconds": "1", "outputs": "DIGEST"}',
        '{"version": 2, "outputs": "DIGEST"}',
        '{"version": 2, "seconds": 1}',
    ],
)
def test_malformed_receipts_certify_nothing(tmp_path: Path, receipt: str):
    """Anything but a well-formed receipt for the current output forces a rebuild."""
    root, base = _repository(tmp_path)
    artifact = _artifact(root, BUNDLE_MODULE, ".olean")
    digest = limits.output_digest(root, BUNDLE)
    stem = artifact.with_suffix("")
    stem.with_name(stem.name + limits.RECEIPT_SUFFIX).write_text(
        receipt.replace("DIGEST", digest)
    )
    assert limits.recorded_seconds(root, BUNDLE) is None
    assert limits.prepare(base, root) == 0
    assert not artifact.exists()


def test_fresh_build_replaces_the_recorded_time(tmp_path: Path):
    """A module compiled in this job is judged by this job's measurement."""
    root, base = _repository(tmp_path)
    _timed(root, base, tmp_path, seconds=865)
    log = tmp_path / "build.log"
    log.write_text(f"Built {BUNDLE_MODULE} (300s)\n")
    assert limits.check(log, base, root, 600) == 0
    assert limits.recorded_seconds(root, BUNDLE) == 300.0


def test_only_changed_modules_get_receipts(tmp_path: Path):
    """Untouched files are outside the limit, so their builds record nothing."""
    root, base = _repository(tmp_path)
    unchanged = "LeanPool/MovingSofa/Certificates/Bundle023.lean"
    _artifact(root, BUNDLE_MODULE, ".olean")
    _artifact(root, "LeanPool.MovingSofa.Certificates.Bundle023", ".olean")
    log = tmp_path / "build.log"
    log.write_text(LAKE_LOG.replace("(865s)", "(300s)"))
    assert limits.check(log, base, root, 600) == 0
    assert limits.recorded_seconds(root, BUNDLE) == 300.0
    assert limits.recorded_seconds(root, unchanged) is None


def test_receipt_without_compiled_output_certifies_nothing(tmp_path: Path, capsys):
    """A receipt naming no output cannot stand in for a module that is not built."""
    root, base = _repository(tmp_path)
    stem = root / ".lake/build/lib/lean" / Path(BUNDLE).with_suffix("")
    stem.parent.mkdir(parents=True)
    receipt = stem.with_name(stem.name + limits.RECEIPT_SUFFIX)
    receipt.write_text(
        json.dumps({"version": limits.RECEIPT_VERSION, "seconds": 1, "outputs": None})
    )
    assert limits.output_digest(root, BUNDLE) is None
    assert limits.recorded_seconds(root, BUNDLE) is None
    assert limits.prepare(base, root) == 0
    assert not receipt.exists()
    receipt.write_text(
        json.dumps({"version": limits.RECEIPT_VERSION, "seconds": 1, "outputs": None})
    )
    log = tmp_path / "build.log"
    log.write_text("")
    capsys.readouterr()
    assert limits.check(log, base, root, 600) == 1
    assert "No successful build timing" in capsys.readouterr().out


def test_missing_output_records_nothing(tmp_path: Path):
    """A timing without compiled output cannot certify a later restore."""
    root, base = _repository(tmp_path)
    log = tmp_path / "build.log"
    log.write_text(f"Built {BUNDLE_MODULE} (300s)\n")
    assert limits.check(log, base, root, 600) == 0
    assert limits.recorded_seconds(root, BUNDLE) is None
    assert limits.output_digest(root, BUNDLE) is None


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


def test_assembly_reuses_output_a_shard_timed(tmp_path: Path):
    """Assembly keeps a shard's delivered output and judges its recorded time."""
    root, base = _repository(tmp_path)
    shard_output = _timed(root, base, tmp_path)
    assert limits.prepare(base, root) == 0
    assert shard_output.exists()
    log = tmp_path / "build.log"
    log.write_text(f"Replayed {BUNDLE_MODULE}\n")
    assert limits.check(log, base, root, 600) == 0


def test_assembly_times_a_shard_project_it_compiles_itself(tmp_path: Path, capsys):
    """Output that never reached assembly is rebuilt there and held to the limit."""
    root, base = _repository(tmp_path)
    undelivered = _artifact(root, BUNDLE_MODULE, ".olean")
    assert limits.prepare(base, root) == 0
    assert not undelivered.exists()
    log = tmp_path / "build.log"
    log.write_text(f"Built {BUNDLE_MODULE} (865s)\n")
    capsys.readouterr()
    assert limits.check(log, base, root, 600) == 1
    assert "took 865 s to build" in capsys.readouterr().out


def test_fresh_slow_build_overrides_a_recorded_passing_time(tmp_path: Path):
    """A module rebuilt over the limit fails although an earlier build passed."""
    root, base = _repository(tmp_path)
    _timed(root, base, tmp_path, seconds=300)
    log = tmp_path / "build.log"
    log.write_text(f"Built {BUNDLE_MODULE} (865s)\n")
    assert limits.check(log, base, root, 600) == 1
    assert limits.recorded_seconds(root, BUNDLE) == 865.0


@pytest.mark.parametrize("command", ["prepare", "check"])
def test_no_job_can_exempt_projects_from_timing(tmp_path: Path, command: str):
    """The command line offers no way to leave a changed project unchecked."""
    arguments = [command, "--base", "HEAD", "--exclude-projects", "MovingSofa"]
    if command == "check":
        arguments += ["--log", str(tmp_path / "build.log")]
    with pytest.raises(SystemExit):
        limits.main(arguments)


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
        # ``prepare`` and ``check`` need the base; ``watch`` takes it when known.
        assert script.count('--base "$time_base"') == 3
        assert (
            ' watch ${time_base:+--base "$time_base"} -- ~/.elan/bin/lake build '
            in script
        )
        assert steps[index]["env"]["BUILD_TIME_BASE"] == (
            "${{ needs.plan.outputs.diff_base }}"
        )
        assert 'git cat-file -e "$BUILD_TIME_BASE"' in script
        assert 'time_base=""' in script
        if name != "rebase":
            assert any("-m lean_pool.ci_pr_build" in s.get("run", "") for s in steps)
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
        assert "--exclude-projects" not in script
        assert "SHARD_PROJECTS" not in steps[index]["env"]
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


@pytest.mark.parametrize("reader", [limits._process_identity, limits._process_state])
def test_a_process_reaped_mid_read_counts_as_gone(monkeypatch, reader) -> None:
    """Reading /proc/PID/stat of a just-reaped process raises ESRCH, not ENOENT."""

    def reaped(self, *args, **kwargs):
        raise ProcessLookupError(3, "No such process")

    monkeypatch.setattr(limits.Path, "read_text", reaped)
    assert reader(os.getpid()) is None
