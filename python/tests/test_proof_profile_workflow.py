"""Regression coverage for automatic PR profiling and its no-files reports."""

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


# Linux refuses to start a process when one environment string exceeds this.
LINUX_SINGLE_STRING_LIMIT = 131072


def test_a_diff_too_large_to_pass_between_jobs_is_reported_not_failed(tmp_path):
    """A migration-sized diff must yield a report instead of a failed plan.

    The v4.36.0 migration changed 3,438 Lean files. Its file list no longer
    fitted one environment variable, so the next step could not start
    ("Argument list too long") and the PR showed a failed advisory check.
    """
    for arguments in (
        ["init", "-q"],
        ["config", "user.name", "Test"],
        ["config", "user.email", "test@example.com"],
    ):
        subprocess.run(["git", *arguments], cwd=tmp_path, check=True)
    project = tmp_path / "LeanPool" / "Migrated"
    project.mkdir(parents=True)
    names = [f"Development{index:04d}{'x' * 40}.lean" for index in range(2500)]
    for name in names:
        (project / name).write_text("theorem probe : True := .intro\n")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "base"], cwd=tmp_path, check=True)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
    ).strip()
    for name in names[:-1]:
        (project / name).write_text("theorem probe : True := trivial\n")
    (project / "Added.lean").write_text("theorem added : True := .intro\n")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "migrate"], cwd=tmp_path, check=True)
    changed = sum(len(f"LeanPool/Migrated/{name} ") for name in names[:-1])
    assert changed > LINUX_SINGLE_STRING_LIMIT

    workflow = yaml.safe_load(WORKFLOW.read_text())
    plan = workflow["jobs"]["plan"]
    selection = next(step for step in plan["steps"] if step.get("id") == "files")
    output = tmp_path / "output"
    subprocess.run(
        ["bash", "-euo", "pipefail", "-c", selection["run"]],
        cwd=tmp_path,
        env={
            **os.environ,
            "BASE_SHA": base,
            "CACHE_MATCHED": "matched",
            "GITHUB_OUTPUT": str(output),
        },
        check=True,
        capture_output=True,
    )
    values = dict(line.split("=", 1) for line in output.read_text().splitlines())
    for name in ("files", "added", "modified", "profile_files", "head_build_modules"):
        assert values[name] == ""
    assert values["compare"] == "false"
    assert "2500 Lean files" in values["skip_note"]
    assert plan["outputs"]["skip_note"] == "${{ steps.files.outputs.skip_note }}"
    # Everything the plan hands to later jobs now fits one variable each.
    assert all(len(value) < LINUX_SINGLE_STRING_LIMIT for value in values.values())

    steps = {step["name"]: step for step in workflow["jobs"]["report"]["steps"]}
    skipped_report = steps["Report no files to profile"]
    assert skipped_report["env"] == {"SKIP_NOTE": "${{ needs.plan.outputs.skip_note }}"}
    summary = tmp_path / "summary.md"
    subprocess.run(
        ["bash", "-euo", "pipefail", "-c", skipped_report["run"]],
        cwd=tmp_path,
        env={
            **os.environ,
            "GITHUB_STEP_SUMMARY": str(summary),
            "SKIP_NOTE": values["skip_note"],
        },
        check=True,
        capture_output=True,
    )
    comment = (tmp_path / "proof-profile.md").read_text()
    assert values["skip_note"] in comment
    assert "No added or modified Lean files" not in comment
    assert "Advisory only" in comment
    assert summary.read_text() == comment


def test_a_large_import_below_the_limit_is_still_profiled(tmp_path):
    """The limit must not silence the profile of an ordinary large import."""
    for arguments in (
        ["init", "-q"],
        ["config", "user.name", "Test"],
        ["config", "user.email", "test@example.com"],
    ):
        subprocess.run(["git", *arguments], cwd=tmp_path, check=True)
    (tmp_path / "README.md").write_text("base\n")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "base"], cwd=tmp_path, check=True)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
    ).strip()
    project = tmp_path / "LeanPool" / "Imported"
    project.mkdir(parents=True)
    for index in range(700):
        (project / f"Development{index:04d}.lean").write_text(
            "theorem probe : True := .intro\n"
        )
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "import"], cwd=tmp_path, check=True)
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
    assert values["skip_note"] == ""
    assert len(values["added"].split()) == 700
    assert values["profile_files"] == values["added"]
