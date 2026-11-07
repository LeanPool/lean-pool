"""Tests for the per-file build-time limits enforced in CI."""

from __future__ import annotations

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


def test_process_table_finds_only_overdue_lean_descendants() -> None:
    """Only Lean processes under the build that ran too long are stopped."""
    table = limits.parse_process_table(
        """\
  100     1    02:00:00 /usr/bin/python3 -m lean_pool.build_time_limits watch
  101   100    02:00:00 /home/runner/.elan/bin/lake build LeanPool
  102   101    01:00:01 /home/runner/.elan/bin/v4/lean LeanPool/A/Slow.lean -o x
  103   101       05:00 /home/runner/.elan/toolchains/v4/bin/lean LeanPool/A/Fast.lean
  104     1    09:00:00 /home/runner/.elan/toolchains/v4/bin/lean Unrelated.lean
  105   101    02:00:00 /bin/sh -c leanc
garbage line
"""
    )
    overdue = limits.overdue_lean_processes(table, root=100, limit=3600)
    assert [process.pid for process in overdue] == [102]
    assert limits.source_of(overdue[0]) == "LeanPool/A/Slow.lean"


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


def test_watch_stops_a_lean_process_past_the_limit(tmp_path: Path) -> None:
    """A Lean process past the hard limit is stopped and the build fails."""
    fake_lean = tmp_path / "lean"
    fake_lean.symlink_to(shutil.which("sleep") or "/bin/sleep")
    build = ["/bin/sh", "-c", f"'{fake_lean}' 60; exit 0"]
    started = time.monotonic()
    assert limits.watch(build, limit=1, poll=0.2) == 124
    assert time.monotonic() - started < 30


def test_watch_passes_through_the_build_status() -> None:
    """Without a stopped process the build exit status is kept."""
    assert limits.watch([sys.executable, "-c", "raise SystemExit(3)"], limit=60) == 3
    assert limits.watch([sys.executable, "-c", "pass"], limit=60) == 0
