"""Regression tests for command heartbeat measurements and rendered reports."""

from __future__ import annotations

import os
import runpy
import subprocess
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[2] / "scripts" / "proof-profile"


def render_report(
    monkeypatch,
    tmp_path,
    head,
    base="",
    modified=False,
    added_files="Probe.lean",
    modified_files="",
    profile_log=None,
):
    """Run the real renderer with isolated measurement logs and GitHub metadata."""
    monkeypatch.chdir(tmp_path)
    for key in ("BASE_SHA", "HEAD_SHA", "COMPARE_NOTE"):
        monkeypatch.delenv(key, raising=False)
    values = {
        "GITHUB_STEP_SUMMARY": str(tmp_path / "summary.md"),
        "GITHUB_SERVER_URL": "https://github.com",
        "GITHUB_REPOSITORY": "Vilin97/lean-pool",
        "GITHUB_RUN_ID": "1",
        "ADDED_FILES": "" if modified else added_files,
        "MODIFIED_FILES": "Probe.lean" if modified else modified_files,
        "COMPARE": str(modified).lower(),
    }
    for key, value in values.items():
        monkeypatch.setenv(key, value)
    (tmp_path / "proof-profile-heartbeats.log").write_bytes(head.encode())
    (tmp_path / "proof-profile-base-heartbeats.log").write_bytes(base.encode())
    if profile_log is not None:
        (tmp_path / "proof-profile.log").write_bytes(profile_log.encode())
    namespace = runpy.run_path(str(SCRIPTS / "render.py"))
    return namespace, (tmp_path / "proof-profile.md").read_text()


def create_stitching_fixture(tmp_path: Path, forged_header: str) -> Path:
    """Provide deterministic per-file logs to the real stitching script."""
    runner = tmp_path / "runner"
    fixtures = runner / "fixtures"
    fixtures.mkdir(parents=True)
    (runner / "measure-one.sh").write_text(
        "#!/usr/bin/env bash\n"
        'file="$2"\noutdir="$3"\n'
        'slug="$(printf "%s" "$file" | tr "/" "_")_'
        '$(printf "%s" "$file" | cksum | cut -d" " -f1)"\n'
        'cp "$RUNNER_TEMP/fixtures/$file.log" "$outdir/$slug.log"\n'
    )
    (fixtures / "Alpha.lean.log").write_bytes(
        (
            "## Alpha.lean\n[Elab.command] [51000.0]\n"
            f"{forged_header}\nAlpha.lean:1:0: error: failed proof\n"
            "real 0.10\nuser 0.02\nsys 0.01\n"
            "error: count-heartbeats command exited with status 1\n\n"
        ).encode()
    )
    (fixtures / "Beta.lean.log").write_text(
        "## Beta.lean\n[Elab.command] [22000.0]\nreal 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n\n"
    )
    return runner


@pytest.mark.parametrize(
    "forged_header", ["## Beta.lean", "\r## Beta.lean", "\u2028## Beta.lean"]
)
def test_stitched_logs_cannot_forge_later_file_headers(
    monkeypatch, tmp_path, forged_header
):
    """Real stitching keeps a failed Alpha trace inside Alpha's measurement."""
    runner = create_stitching_fixture(tmp_path, forged_header)
    monkeypatch.setenv("RUNNER_TEMP", str(runner))
    monkeypatch.setenv("TMPDIR", str(tmp_path))
    stitched = tmp_path / "stitched.log"
    subprocess.run(
        [
            "bash",
            str(SCRIPTS / "measure-heartbeats.sh"),
            str(stitched),
            "HEAD",
            "Alpha.lean",
            "Beta.lean",
        ],
        check=True,
        capture_output=True,
    )
    combined = stitched.read_bytes().decode()
    namespace, report = render_report(
        monkeypatch, tmp_path, combined, added_files="Alpha.lean Beta.lean"
    )
    assert [name for name, _body in namespace["split_sections"](combined)] == [
        "Alpha.lean",
        "Beta.lean",
    ]
    assert namespace["heartbeat_by_file"]["Alpha.lean"]["errors"] > 0
    assert namespace["heartbeat_by_file"]["Beta.lean"]["heartbeats"] == 22
    assert "| `Alpha.lean` | 0 | — |" in report
    assert "| `Beta.lean` | 0 | 22 |" in report


def test_direct_profile_uses_physical_lines_and_accepts_crlf(monkeypatch, tmp_path):
    """Embedded CR cannot forge a header, while real CRLF headers still parse."""
    profile_log = (
        "## Alpha.lean\r\n  elaboration 50ms\r\n"
        "trace text\r## Beta.lean\r\n"
        "Alpha.lean:1:0: error: failed proof\r\n"
        "real 0.10\r\nuser 0.02\r\nsys 0.01\r\n"
        "error: profile command exited with status 1\r\n"
        "## Beta.lean\r\n  elaboration 20ms\r\n"
        "real 0.20\r\nuser 0.03\r\nsys 0.01\r\n"
    )
    namespace, report = render_report(
        monkeypatch,
        tmp_path,
        "",
        added_files="Alpha.lean",
        modified_files="Beta.lean",
        profile_log=profile_log,
    )
    assert namespace["profile_boundaries_valid"] is True
    assert namespace["profile_by_file"]["Alpha.lean"]["total_ms"] is None
    assert namespace["profile_by_file"]["Alpha.lean"]["errors"] == 2
    assert namespace["profile_by_file"]["Beta.lean"]["total_ms"] == 20
    assert namespace["phase_totals"] == {"elaboration": 20}
    assert "**Sum of `lean --profile`:** 20.0 ms (= 0.02 s)" in report
    assert "across 1 valid file" in report
    assert "| `Alpha.lean` | 0 | — | — | — | — | — |" in report
    assert "`lean --profile` timings unavailable" not in report


def test_zero_phase_profile_is_unavailable(monkeypatch, tmp_path):
    """A completed wrapper without Lean phase output has no measured time."""
    namespace, report = render_report(
        monkeypatch,
        tmp_path,
        "",
        profile_log="## Probe.lean\nreal 0.10\nuser 0.02\nsys 0.01\n",
    )
    assert namespace["profile_by_file"]["Probe.lean"]["total_ms"] is None
    assert namespace["profile_by_file"]["Probe.lean"]["errors"] == 1
    assert namespace["phase_totals"] == {}
    assert "**Sum of `lean --profile`:** — across 0 valid files" in report


def test_successful_profile_keeps_benign_error_text(monkeypatch, tmp_path):
    """Only the wrapper's terminal failure marker invalidates real phases."""
    namespace, report = render_report(
        monkeypatch,
        tmp_path,
        "",
        profile_log=(
            "## Probe.lean\nerror: harmless trace text\n"
            "  elaboration 50ms\nreal 0.10\nuser 0.02\nsys 0.01\n"
        ),
    )
    assert namespace["profile_by_file"]["Probe.lean"]["total_ms"] == 50
    assert namespace["phase_totals"] == {"elaboration": 50}
    assert "across 1 valid file" in report


def test_incomplete_profile_keeps_completed_sibling(monkeypatch, tmp_path):
    """A truncated timed run cannot erase another file's valid phase totals."""
    profile_log = (
        "## Alpha.lean\n  elaboration 50ms\nreal 0.10\n"
        "## Beta.lean\n  elaboration 20ms\n"
        "real 0.20\nuser 0.03\nsys 0.01\n"
    )
    namespace, report = render_report(
        monkeypatch,
        tmp_path,
        "",
        added_files="Alpha.lean Beta.lean",
        profile_log=profile_log,
    )
    assert namespace["profile_headers_valid"] is True
    assert namespace["profile_boundaries_valid"] is False
    assert namespace["profile_by_file"]["Alpha.lean"]["total_ms"] is None
    assert namespace["profile_by_file"]["Alpha.lean"]["errors"] > 0
    assert namespace["profile_by_file"]["Alpha.lean"]["wall_seconds"] is None
    assert namespace["profile_by_file"]["Beta.lean"]["total_ms"] == 20
    assert namespace["phase_totals"] == {"elaboration": 20}
    assert "Some `lean --profile` timings unavailable" in report
    assert "**Sum of `lean --profile`:** 20.0 ms (= 0.02 s)" in report
    assert "across 1 valid file" in report


@pytest.mark.parametrize(
    "profile_log",
    [
        "## Alpha.lean\n  elaboration 50ms\n## Beta.lean\n"
        "Alpha.lean:1:0: error: failed\n## Beta.lean\n  elaboration 20ms\n",
        "## Alpha.lean\n  elaboration 50ms\n",
        "## Beta.lean\n  elaboration 20ms\n## Alpha.lean\n  elaboration 50ms\n",
        "## Alpha.lean\n  elaboration 50ms\n"
        "## Gamma.lean\n  elaboration 20ms\n"
        "## Beta.lean\n  elaboration 20ms\n",
    ],
)
def test_ambiguous_direct_profile_headers_hide_all_profile_times(
    monkeypatch, tmp_path, profile_log
):
    """Direct log ambiguity cannot silently overwrite a failed file's profile."""
    heartbeats = (
        "## Alpha.lean\n[Elab.command] [51000.0]\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
        "## Beta.lean\n[Elab.command] [22000.0]\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    namespace, report = render_report(
        monkeypatch,
        tmp_path,
        heartbeats,
        added_files="Alpha.lean Beta.lean",
        profile_log=profile_log,
    )
    assert "`lean --profile` timings unavailable" in report
    assert namespace["profile_boundaries_valid"] is False
    assert namespace["profile_by_file"] == {}
    assert namespace["phase_totals"] == {}
    assert "`lean --profile` timings unavailable" in report
    assert "**Sum of `lean --profile`:** —" in report
    assert "| `Alpha.lean` | 0 | 51 | 0.10 | — | — | — |" in report
    assert "| `Beta.lean` | 0 | 22 | 0.10 | — | — | — |" in report


def test_direct_profile_expects_only_added_files_during_comparison(
    monkeypatch, tmp_path
):
    """A modified file header is unexpected when its profile is comparative."""
    heartbeat = (
        "## Probe.lean\n[Elab.command] [51000.0]\nreal 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    namespace, report = render_report(
        monkeypatch,
        tmp_path,
        heartbeat,
        heartbeat,
        modified=True,
        profile_log="## Probe.lean\n  elaboration 50ms\n",
    )
    assert "`lean --profile` timings unavailable" in report
    assert namespace["expected_profile_files"] == []
    assert namespace["profile_boundaries_valid"] is False
    assert "`lean --profile` timings unavailable" in report


def test_command_totals_exclude_nested_traces(monkeypatch, tmp_path):
    """Count disjoint commands once and convert raw heartbeats to user units."""
    log = """## Probe.lean
[Elab.command] [51000.000000] ✅️ theorem probe := by norm_num
  [Elab.command] [40000.000000] ✅️ nested command
  [Elab.step] [20000.000000] ✅️ nested elaboration
[Elab.command] [12500.000000] ✅️ def twice := 2
real 1.25
user 0.25
sys 0.10
success: count-heartbeats command exited with status 0
"""
    namespace, report = render_report(monkeypatch, tmp_path, log)
    data = namespace["heartbeat_by_file"]["Probe.lean"]
    assert data["heartbeats"] == 63.5
    assert data["declarations"] == 2
    assert data["errors"] == 0
    assert data["wall_seconds"] == 1.25
    assert "Commands | Errors" in report


def test_source_heartbeat_messages_do_not_double_count(monkeypatch, tmp_path):
    """Direct counters inside source must not contaminate the command totals."""
    log = (
        "## Probe.lean\nUsed 51 heartbeats\n[Elab.command] [100000.0]\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    namespace, report = render_report(monkeypatch, tmp_path, log)
    data = namespace["heartbeat_by_file"]["Probe.lean"]
    assert data["heartbeats"] == 100
    assert data["errors"] == 0
    assert "Legacy heartbeat measurements rejected" not in report


@pytest.mark.parametrize(
    "command",
    [
        'def message : String := "error: harmless text"',
        'theorem probe : True := by\n  let message := "error: harmless text"\n'
        "  exact True.intro",
        'def message : String := "Probe.lean:1:0: error: harmless text"',
    ],
)
def test_echoed_error_literals_are_successful_measurements(
    monkeypatch, tmp_path, command
):
    """Echoed source literals must not discard valid totals or comparisons."""
    head = (
        f"## Probe.lean\n[Elab.command] [51000.0] ✅️ {command}\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    base = (
        "## Probe.lean\n[Elab.command] [51000.0] ✅️ theorem probe\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    namespace, report = render_report(monkeypatch, tmp_path, head, base, modified=True)
    data = namespace["heartbeat_by_file"]["Probe.lean"]
    assert data["heartbeats"] == 51
    assert data["declarations"] == 1
    assert data["errors"] == 0
    assert namespace["compared"] == ["Probe.lean"]
    assert "51 → 51" in report


@pytest.mark.parametrize(
    "message",
    [
        "error: count-heartbeats command exited with status 1",
        "error: could not read Probe.lean at revision HEAD",
        "Probe.lean:1:0: error: harmless trace text",
    ],
)
def test_bare_trace_error_literals_are_successful_measurements(
    monkeypatch, tmp_path, message
):
    """A successful Lean trace cannot impersonate the wrapper's final status."""
    head = (
        "## Probe.lean\n"
        f'[Elab.command] [51000.0] ✅️ theorem probe := by trace "{message}"\n'
        f"{message}\nreal 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    base = (
        "## Probe.lean\n[Elab.command] [51000.0] ✅️ theorem probe\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    namespace, report = render_report(monkeypatch, tmp_path, head, base, modified=True)
    data = namespace["heartbeat_by_file"]["Probe.lean"]
    assert data["heartbeats"] == 51
    assert data["declarations"] == 1
    assert data["errors"] == 0
    assert namespace["compared"] == ["Probe.lean"]
    assert "51 → 51" in report


@pytest.mark.parametrize(
    "body",
    [
        "'probe' used 4 heartbeats, which is less than the current maximum of 200000.",
        "Used approximately 4000 heartbeats",
    ],
)
def test_legacy_counts_are_unavailable(monkeypatch, tmp_path, body):
    """Old linter results must not be presented as valid cheap proofs."""
    namespace, report = render_report(monkeypatch, tmp_path, f"## Probe.lean\n{body}\n")
    data = namespace["heartbeat_by_file"]["Probe.lean"]
    assert data["errors"] == 1
    assert data["heartbeats"] == 0
    assert "Legacy heartbeat measurements rejected" in report
    assert "**Total heartbeats:** —" in report


@pytest.mark.parametrize(
    "body",
    [
        "warning: no measurements",
        "[Elab.command] [1000.0]\nProbe.lean:1:0: error: bad proof",
        "[Elab.command] [1000.0]\nProbe.lean:1:0: error: bad proof\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "error: count-heartbeats command exited with status 1",
        "[Elab.command] [1000.0]\nreal 0.10\nuser 0.02\nsys 0.01\n"
        "error: count-heartbeats command exited with status 137",
        "error: could not read Probe.lean at revision HEAD",
    ],
)
def test_missing_or_failed_measurements_are_unavailable(monkeypatch, tmp_path, body):
    """Missing instrumentation and partial failed elaborations cannot enter totals."""
    namespace, report = render_report(monkeypatch, tmp_path, f"## Probe.lean\n{body}\n")
    assert namespace["heartbeat_by_file"]["Probe.lean"]["errors"] > 0
    assert "**Total heartbeats:** —" in report


def test_failed_head_is_not_a_performance_improvement(monkeypatch, tmp_path):
    """A failed measurement must not be classified as a heartbeat reduction."""
    base = (
        "## Probe.lean\n[Elab.command] [5000000.0] ✅️ theorem probe\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    head = "## Probe.lean\n'probe' used 4 heartbeats\n"
    namespace, report = render_report(monkeypatch, tmp_path, head, base, modified=True)
    assert namespace["compared"] == []
    assert "cheaper" not in report


@pytest.mark.parametrize("partial_side", ["base", "head"])
@pytest.mark.parametrize(
    "tail",
    [
        "",
        "real 0.10\n",
        "real 0.10\nuser 0.02\n",
        "real 0.10\nuser 0.02\nsys 0.01\n",
    ],
)
def test_truncated_heartbeat_trace_is_unavailable(
    monkeypatch, tmp_path, partial_side, tail
):
    """Partial command traces cannot enter either side of a comparison."""
    complete = (
        "## Probe.lean\n[Elab.command] [5000000.0] ✅️ theorem probe\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    partial = "## Probe.lean\n[Elab.command] [2000000.0] ✅️ theorem probe\n" + tail
    base, head = (partial, complete) if partial_side == "base" else (complete, partial)
    namespace, report = render_report(monkeypatch, tmp_path, head, base, modified=True)
    data = (
        namespace["base_heartbeat_by_file"]["Probe.lean"]
        if partial_side == "base"
        else namespace["heartbeat_by_file"]["Probe.lean"]
    )
    assert data["errors"] == 1
    assert data["heartbeats"] == 0
    assert data["wall_seconds"] is None
    assert namespace["compared"] == []
    assert "1 cheaper" not in report


def test_successful_comparison_uses_command_units(monkeypatch, tmp_path):
    """A real proof-work reduction retains the base-to-head comparison."""
    base = (
        "## Probe.lean\n[Elab.command] [5000000.0] ✅️ theorem probe\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    head = (
        "## Probe.lean\n[Elab.command] [2000000.0] ✅️ theorem probe\n"
        "real 0.10\nuser 0.02\nsys 0.01\n"
        "success: count-heartbeats command exited with status 0\n"
    )
    namespace, report = render_report(monkeypatch, tmp_path, head, base, modified=True)
    assert namespace["compared"] == ["Probe.lean"]
    assert "1 cheaper" in report
    assert "5,000 → 2,000" in report


def create_real_measurement_project(
    workspace: Path, project: Path, module_mode: bool
) -> None:
    """Create a pinned-toolchain Git fixture for the real Lean profiler test."""
    project.mkdir()
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        (project / name).write_bytes((workspace / name).read_bytes())
    (project / ".lake").mkdir()
    (project / ".lake/packages").symlink_to(workspace / ".lake/packages")
    source = """import Mathlib.Util.CountHeartbeats
import Mathlib.Tactic.NormNum
theorem probe : True := by
  trace "HEARTBEAT_PROOF_EXECUTED"
  have h : (2 : Nat)^100 = 1267650600228229401496703205376 := by norm_num
  exact True.intro
"""
    if module_mode:
        source = "module\n" + source.replace("theorem probe", "public theorem probe")
    (project / "Probe.lean").write_text(source)
    for arguments in (
        ["init", "-q"],
        ["add", "Probe.lean"],
        [
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "fixture",
        ],
    ):
        subprocess.run(
            ["git", *arguments], cwd=project, check=True, capture_output=True
        )


@pytest.mark.skipif(
    not os.environ.get("LEAN_POOL_HEARTBEAT_WORKSPACE"),
    reason="needs the pinned Lean toolchain and prebuilt Mathlib",
)
@pytest.mark.parametrize("module_mode", [False, True])
def test_real_measurement_counts_proof_once(monkeypatch, tmp_path, module_mode):
    """Exercise git-source extraction, Lean elaboration, and rendering end to end."""
    workspace = Path(os.environ["LEAN_POOL_HEARTBEAT_WORKSPACE"])
    project = tmp_path / "project"
    create_real_measurement_project(workspace, project, module_mode)
    logs = tmp_path / "logs"
    logs.mkdir()
    subprocess.run(
        ["bash", str(SCRIPTS / "measure-one.sh"), "HEAD", "Probe.lean", str(logs)],
        cwd=project,
        check=True,
        capture_output=True,
        timeout=60,
    )
    log = next(logs.glob("*.log")).read_text()
    assert "error:" not in log
    assert "has already been declared" not in log
    assert "[Elab.command]" in log
    assert log.count("\nHEARTBEAT_PROOF_EXECUTED\n") == 1
    namespace, _ = render_report(monkeypatch, tmp_path, log)
    data = namespace["heartbeat_by_file"]["Probe.lean"]
    assert data["errors"] == 0
    assert data["heartbeats"] > 20
