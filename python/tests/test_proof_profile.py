"""Regression tests for command heartbeat measurements and rendered reports."""

from __future__ import annotations

import os
import runpy
import subprocess
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[2] / "scripts" / "proof-profile"


def render_report(monkeypatch, tmp_path, head, base="", modified=False):
    """Run the real renderer with isolated measurement logs and GitHub metadata."""
    monkeypatch.chdir(tmp_path)
    for key in ("BASE_SHA", "HEAD_SHA", "COMPARE_NOTE"):
        monkeypatch.delenv(key, raising=False)
    values = {
        "GITHUB_STEP_SUMMARY": str(tmp_path / "summary.md"),
        "GITHUB_SERVER_URL": "https://github.com",
        "GITHUB_REPOSITORY": "Vilin97/lean-pool",
        "GITHUB_RUN_ID": "1",
        "ADDED_FILES": "" if modified else "Probe.lean",
        "MODIFIED_FILES": "Probe.lean" if modified else "",
        "COMPARE": str(modified).lower(),
    }
    for key, value in values.items():
        monkeypatch.setenv(key, value)
    (tmp_path / "proof-profile-heartbeats.log").write_text(head)
    (tmp_path / "proof-profile-base-heartbeats.log").write_text(base)
    namespace = runpy.run_path(str(SCRIPTS / "render.py"))
    return namespace, (tmp_path / "proof-profile.md").read_text()


def test_command_totals_exclude_nested_traces(monkeypatch, tmp_path):
    """Count disjoint commands once and convert raw heartbeats to user units."""
    log = """## Probe.lean
[Elab.command] [51000.000000] ✅️ theorem probe := by norm_num
  [Elab.command] [40000.000000] ✅️ nested command
  [Elab.step] [20000.000000] ✅️ nested elaboration
[Elab.command] [12500.000000] ✅️ def twice := 2
real 1.25
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
    log = "## Probe.lean\nUsed 51 heartbeats\n[Elab.command] [100000.0]\n"
    namespace, report = render_report(monkeypatch, tmp_path, log)
    data = namespace["heartbeat_by_file"]["Probe.lean"]
    assert data["heartbeats"] == 100
    assert data["errors"] == 0
    assert "Legacy heartbeat measurements rejected" not in report


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
    assert data["errors"] > 0
    assert data["heartbeats"] == 0
    assert "Legacy heartbeat measurements rejected" in report
    assert "**Total heartbeats:** —" in report


@pytest.mark.parametrize(
    "body", ["warning: no measurements", "[Elab.command] [1000.0]\nerror: bad proof"]
)
def test_missing_or_failed_measurements_are_unavailable(monkeypatch, tmp_path, body):
    """Missing instrumentation and partial failed elaborations cannot enter totals."""
    namespace, report = render_report(monkeypatch, tmp_path, f"## Probe.lean\n{body}\n")
    assert namespace["heartbeat_by_file"]["Probe.lean"]["errors"] > 0
    assert "**Total heartbeats:** —" in report


def test_failed_head_is_not_a_performance_improvement(monkeypatch, tmp_path):
    """A failed measurement must not be classified as a heartbeat reduction."""
    base = "## Probe.lean\n[Elab.command] [5000000.0] ✅️ theorem probe\n"
    head = "## Probe.lean\n'probe' used 4 heartbeats\n"
    namespace, report = render_report(monkeypatch, tmp_path, head, base, modified=True)
    assert namespace["compared"] == []
    assert "cheaper" not in report


def test_successful_comparison_uses_command_units(monkeypatch, tmp_path):
    """A real proof-work reduction retains the base-to-head comparison."""
    base = "## Probe.lean\n[Elab.command] [5000000.0] ✅️ theorem probe\n"
    head = "## Probe.lean\n[Elab.command] [2000000.0] ✅️ theorem probe\n"
    namespace, report = render_report(monkeypatch, tmp_path, head, base, modified=True)
    assert namespace["compared"] == ["Probe.lean"]
    assert "1 cheaper" in report
    assert "5,000 → 2,000" in report


@pytest.mark.skipif(
    not os.environ.get("LEAN_POOL_HEARTBEAT_WORKSPACE"),
    reason="needs the pinned Lean toolchain and prebuilt Mathlib",
)
@pytest.mark.parametrize("module_mode", [False, True])
def test_real_measurement_counts_proof_once(monkeypatch, tmp_path, module_mode):
    """Exercise git-source extraction, Lean elaboration, and rendering end to end."""
    workspace = Path(os.environ["LEAN_POOL_HEARTBEAT_WORKSPACE"])
    project = tmp_path / "project"
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
