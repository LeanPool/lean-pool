"""Regression coverage for automatic PR profiling and its no-files report."""

import os
import subprocess
from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[2] / ".github/workflows/proof-profile.yml"


def test_every_pr_update_can_start_a_profile():
    """Keep automatic events wired through both admission and concurrency."""
    workflow = yaml.safe_load(WORKFLOW.read_text())
    events = workflow.get("on", workflow.get(True))
    assert set(events["pull_request"]["types"]) == {
        "opened",
        "synchronize",
        "reopened",
        "ready_for_review",
    }
    for expression in (
        workflow["jobs"]["plan"]["if"],
        workflow["concurrency"]["group"],
    ):
        assert "github.event_name == 'pull_request' ||" in expression
        assert "draft" not in expression
    assert "issue_comment" in events
    assert "workflow_dispatch" in events


def test_no_lean_changes_still_produce_a_comment(tmp_path):
    """Execute the no-files report used when all measurement jobs are skipped."""
    workflow = yaml.safe_load(WORKFLOW.read_text())
    report = workflow["jobs"]["report"]
    assert "needs.plan.outputs.files" not in report["if"]
    steps = {step["name"]: step for step in report["steps"]}
    empty_report = steps["Report no files to profile"]
    assert empty_report["if"] == "needs.plan.outputs.files == ''"
    for name in ("Download measurement logs", "Render profile summary"):
        assert steps[name]["if"] == "needs.plan.outputs.files != ''"
    summary = tmp_path / "summary.md"
    subprocess.run(
        ["bash", "-euo", "pipefail", "-c", empty_report["run"]],
        cwd=tmp_path,
        env={**os.environ, "GITHUB_STEP_SUMMARY": str(summary)},
        check=True,
        capture_output=True,
    )
    comment = (tmp_path / "proof-profile.md").read_text()
    assert "No added or modified Lean files" in comment
    assert summary.read_text() == comment
    assert (
        "needs.plan.outputs.files"
        not in steps["Post sticky PR comment (writable-token runs)"]["if"]
    )


def test_forks_keep_the_artifact_comment_path():
    """Read-only fork runs must stage the same report for the writable poster."""
    workflow = yaml.safe_load(WORKFLOW.read_text())
    steps = {step["name"]: step for step in workflow["jobs"]["report"]["steps"]}
    direct = steps["Post sticky PR comment (writable-token runs)"]["if"]
    assert "github.event_name != 'pull_request'" in direct
    assert (
        "github.event.pull_request.head.repo.full_name == github.repository" in direct
    )
    for name in (
        "Stage comment payload for the companion workflow",
        "Upload comment payload",
    ):
        assert "steps.direct_post.outcome != 'success'" in steps[name]["if"]


def test_renamed_lean_files_are_profiled(tmp_path):
    """A pure rename must produce an added file instead of an empty profile."""
    for arguments in (
        ["init", "-q"],
        ["config", "user.name", "Test"],
        ["config", "user.email", "test@example.com"],
    ):
        subprocess.run(["git", *arguments], cwd=tmp_path, check=True)
    project = tmp_path / "LeanPool"
    project.mkdir()
    source = project / "Before.lean"
    source.write_text("theorem probe : True := .intro\n")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "base"], cwd=tmp_path, check=True)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
    ).strip()
    source.rename(project / "After.lean")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "rename"], cwd=tmp_path, check=True)
    workflow = yaml.safe_load(WORKFLOW.read_text())
    selection = next(
        step for step in workflow["jobs"]["plan"]["steps"] if step.get("id") == "files"
    )
    output = tmp_path / "output"
    subprocess.run(
        ["bash", "-euo", "pipefail", "-c", selection["run"]],
        cwd=tmp_path,
        env={
            **os.environ,
            "BASE_SHA": base,
            "CACHE_MATCHED": "",
            "GITHUB_OUTPUT": str(output),
        },
        check=True,
        capture_output=True,
    )
    values = dict(line.split("=", 1) for line in output.read_text().splitlines())
    assert values["added"].strip() == "LeanPool/After.lean"
    assert values["profile_files"].strip() == "LeanPool/After.lean"
