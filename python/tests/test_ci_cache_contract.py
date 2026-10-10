"""Keep shared cache producers and consumers compatible across CI workflows."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest
import yaml

WORKFLOWS = Path(__file__).resolve().parents[2] / ".github/workflows"


def test_shared_cache_paths_and_keys_match() -> None:
    """Cache versions include paths, so consumers must match the producer's contract."""
    contracts = {}
    producers = {}
    for path in WORKFLOWS.glob("*.yml"):
        workflow = yaml.safe_load(path.read_text())
        for job in workflow.get("jobs", {}).values():
            for step in job.get("steps", []):
                if not step.get("uses", "").startswith("actions/cache/"):
                    continue
                settings = step.get("with", {})
                key = settings.get("key", "")
                if key.startswith("LeanDependencies-v1-"):
                    category = "dependencies"
                    identity = key
                elif key.startswith("LeanPoolBuild-v1-"):
                    category = "build"
                    identity = key.rsplit("-${{", 1)[0] + "-"
                    if "restore-keys" in settings:
                        assert settings["restore-keys"].strip() == identity
                else:
                    continue
                paths = tuple(settings["path"].strip().splitlines())
                contract = (identity, paths)
                assert contracts.setdefault(category, contract) == contract, path
                if step["uses"].startswith("actions/cache/save@"):
                    producers[category] = True
    assert set(producers) == set(contracts) == {"dependencies", "build"}
    assert contracts["dependencies"][1] == ("~/.elan", ".lake/packages")
    assert contracts["build"][1] == (".lake/build",)


def _docs_condition(condition: str, event: str, ref: str, preview: bool, readme: bool):
    """Evaluate the small event predicate used by docs job allocation."""
    expression = condition
    values = {
        "needs.preflight.outputs.readme_only": repr(str(readme).lower()),
        "github.event_name": repr(event),
        "github.ref": repr(ref),
        "inputs.preview": repr(preview),
    }
    for name, value in values.items():
        expression = expression.replace(name, value)
    return eval(
        expression.replace("&&", " and ").replace("||", " or "),
        {"__builtins__": {}},
        {},
    )


def test_docs_generate_on_main_and_explicit_preview_only() -> None:
    """PRs scope preflight without allocating heavy docs runners."""
    jobs = yaml.safe_load((WORKFLOWS / "docs.yml").read_text())["jobs"]
    assert jobs["preflight"]["name"] == "Documentation preflight"
    assert jobs["preflight"]["needs"] == "scope"
    scenarios = [
        ("pull_request", "refs/pull/123/merge", False, False, False),
        ("push", "refs/heads/main", False, False, True),
        ("workflow_dispatch", "refs/heads/main", False, False, True),
        ("workflow_dispatch", "refs/heads/topic", False, False, False),
        ("workflow_dispatch", "refs/heads/topic", True, False, True),
        ("pull_request", "refs/pull/123/merge", True, False, False),
        ("push", "refs/heads/main", False, True, False),
    ]
    for name in ("exposition", "mathlib_doc_info", "build"):
        for event, ref, preview, readme, expected in scenarios:
            assert (
                _docs_condition(jobs[name]["if"], event, ref, preview, readme)
                == expected
            )
    # Branch previews produce artifacts but cannot replace production Pages.
    assert not _docs_condition(
        jobs["deployment_freshness"]["if"],
        "workflow_dispatch",
        "refs/heads/topic",
        True,
        False,
    )


def test_single_and_sharded_builds_use_validation_cache() -> None:
    """Both execution paths validate before saving receipts and keep the same gate."""
    jobs = yaml.safe_load((WORKFLOWS / "lean_action_ci.yml").read_text())["jobs"]
    assert jobs["gate"]["name"] == "Build project"
    contracts = []
    for job in ("build", "finalize"):
        steps = jobs[job]["steps"]
        names = [step.get("name") for step in steps]
        assert names.index("Restore project validation") < names.index("Lint")
        assert names.index("Repository quality checks") < names.index(
            "Save project validation"
        )
        restore = steps[names.index("Restore project validation")]
        save = steps[names.index("Save project validation")]
        assert restore["with"]["key"] == save["with"]["key"]
        assert (
            restore["with"]["path"]
            == save["with"]["path"]
            == ".lake/validation-cache/v1"
        )
        assert "if" not in save  # normal success guard, including PR updates
        contracts.append(restore["with"])
        assert "validation_cache lint" in steps[names.index("Lint")]["run"]
        assert "lint-style LeanPool" in steps[names.index("Text style lint")]["run"]
    assert contracts[0] == contracts[1]


def test_merge_queue_reports_all_required_gates_without_path_filtered_workflows() -> (
    None
):
    """A filtered-out workflow must never leave the protected queue waiting forever."""
    import json

    rules = json.loads((WORKFLOWS.parent / "merge-queue-ruleset.json").read_text())[
        "rules"
    ]
    required = {
        check["context"]
        for rule in rules
        if rule["type"] == "required_status_checks"
        for check in rule["parameters"]["required_status_checks"]
    }
    names = set()
    for filename in (
        "lean_action_ci.yml",
        "content-pr-guard.yml",
        "docs.yml",
        "python_ci.yml",
        "workflow_lint.yml",
        "exposition-verify.yml",
    ):
        workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
        events = workflow.get("on", workflow.get(True))
        assert "merge_group" in events
        if filename != "content-pr-guard.yml":
            assert "paths" not in events["pull_request"]
        names.update(job.get("name", key) for key, job in workflow["jobs"].items())
    assert required <= names
    queue = next(rule["parameters"] for rule in rules if rule["type"] == "merge_queue")
    assert queue["grouping_strategy"] == "ALLGREEN"
    assert queue["merge_method"] == "SQUASH"


def test_yaml_aware_recovery_has_a_declared_runtime_in_every_job() -> None:
    """Early planning and restore steps cannot depend on runner-global PyYAML."""
    modules = ("rebase_fastpath", "ci_pr_build", "queue_build")
    for filename in ("lean_action_ci.yml", "docs.yml", "exposition-verify.yml"):
        workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
        for job in workflow["jobs"].values():
            runtime_available = False
            for step in job["steps"]:
                if str(step.get("uses", "")).startswith("astral-sh/setup-uv@"):
                    runtime_available = True
                command = step.get("run", "")
                if any(f"-m lean_pool.{module}" in command for module in modules):
                    assert runtime_available, (filename, step)
                    assert "uv run --project python --locked python -m" in command
                    assert not any(
                        f"python3 -m lean_pool.{module}" in command
                        for module in modules
                    )


def test_required_scoped_checks_fail_closed_when_classification_fails() -> None:
    """A broken classifier cannot turn a required validation into a passing skip."""
    for filename, names in (
        ("python_ci.yml", ("lint", "test")),
        ("exposition-verify.yml", ("verify",)),
        ("docs.yml", ("preflight",)),
        ("workflow_lint.yml", ("actionlint", "pinned-actions")),
    ):
        workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
        for name in names:
            job = workflow["jobs"][name]
            assert job["if"] == (
                "always() && (needs.scope.result != 'success' || "
                "needs.scope.outputs.applicable != 'false')"
            )
            guard = job["steps"][0]
            assert (
                guard["env"].items()
                >= {
                    "SCOPE_RESULT": "${{ needs.scope.result }}",
                    "APPLICABLE": "${{ needs.scope.outputs.applicable }}",
                }.items()
            )
            for result, applicable, accepted in (
                ("success", "true", True),
                ("failure", "true", False),
                ("failure", "", False),
                ("cancelled", "false", False),
                ("success", "", False),
            ):
                process = subprocess.run(
                    ["bash", "-e", "-c", guard["run"]],
                    env={
                        **os.environ,
                        "SCOPE_RESULT": result,
                        "APPLICABLE": applicable,
                        "BUILD_READY_RESULT": "success",
                        "EVENT": "pull_request",
                    },
                    capture_output=True,
                )
                assert (process.returncode == 0) == accepted


def test_minimal_verifier_pr_has_an_explicit_project_build_producer(tmp_path):
    """Minimal verification overlays only the PR's projects and retains its gate."""
    lean = yaml.safe_load((WORKFLOWS / "lean_action_ci.yml").read_text())["jobs"]
    minimal = yaml.safe_load((WORKFLOWS / "exposition-verify.yml").read_text())["jobs"]
    assert "minimal_build" in lean["plan"]["outputs"]
    planning = next(step for step in lean["plan"]["steps"] if step.get("id") == "plan")
    classifier = minimal["scope"]["steps"][-1]["run"]
    # Producer scope must include precisely the consumer's heavy trigger paths.
    pattern = classifier.split("grep -Eq '")[1].split("'")[0]
    assert pattern in planning["run"]
    classification = (
        "minimal_build=false"
        + planning["run"]
        .split("minimal_build=false", 1)[1]
        .split("dependency_tests=true", 1)[0]
    )
    changed = tmp_path / "changed-files.txt"
    output = tmp_path / "output.txt"
    for path, event, expected in (
        ("python/lean_pool/ci_artifacts.py", "pull_request", "true"),
        ("python/lean_pool/exposition/verify.py", "pull_request", "true"),
        ("scripts/exposition/extract-all.sh", "pull_request", "true"),
        (".github/workflows/exposition-verify.yml", "pull_request", "true"),
        ("LeanPool/projects/example.yaml", "pull_request", "false"),
        ("python/lean_pool/registry.py", "pull_request", "false"),
        ("python/lean_pool/exposition/verify.py", "merge_group", "false"),
    ):
        changed.write_text(path + "\n")
        output.write_text("")
        subprocess.run(
            ["bash", "-e", "-c", classification],
            env={
                **os.environ,
                "changed_files": str(changed),
                "GITHUB_OUTPUT": str(output),
                "EVENT_NAME": event,
            },
            check=True,
        )
        assert output.read_text().strip() == f"minimal_build={expected}"
    for name in ("build", "finalize"):
        steps = {step.get("name"): step for step in lean[name]["steps"]}
        for producer in (
            "Package build for documentation",
            "Share build with documentation",
        ):
            assert "needs.plan.outputs.minimal_build == 'true'" in steps[producer]["if"]
            assert "github.event_name == 'pull_request'" in steps[producer]["if"]
        package = steps["Package build for documentation"]["run"]
        assert 'if [ "$BUILD_EVENT" = pull_request ]' in package
        assert 'pack --base "$BASE_SHA" --head "$HEAD_SHA"' in package
    steps = {step.get("name"): step for step in minimal["verify"]["steps"]}
    reuse = steps["Reuse matching Lean CI build"]
    assert "github.event_name != 'pull_request'" not in reuse["if"]
    assert "--pull-request-artifact" in reuse["run"]
    assert "--wait-seconds 0" in reuse["run"]
    assert steps["Build pool"]["run"] == "~/.elan/bin/lake build LeanPool"
    assert "--baseline 214" in steps["Verify minimal files"]["run"]


def test_assembly_restores_projects_once_and_main_owns_full_cache():
    """Assembly recovers PR outputs once before fresh shard files are applied."""
    jobs = yaml.safe_load((WORKFLOWS / "lean_action_ci.yml").read_text())["jobs"]
    assert not any(
        "lean_pool.ci_pr_build" in step.get("run", "")
        or "lean_pool.queue_build" in step.get("run", "")
        for step in jobs["shard"]["steps"]
    )
    steps = jobs["finalize"]["steps"]
    names = [step.get("name") for step in steps]
    assert names.index(
        "Reuse compiled files from this PR's successful runs"
    ) < names.index("Download shard build outputs")
    assert names.index("Reuse successful queued PR builds") < names.index(
        "Build project"
    )
    for job in jobs.values():
        for step in job["steps"]:
            if step.get("uses", "").startswith("actions/cache/save@"):
                key = step["with"]["key"]
                if key.startswith(("LeanPoolBuild-", "LeanDependencies-")):
                    assert "github.ref == 'refs/heads/main'" in step["if"]


def test_extraction_caches_survive_failure_and_retry_keys_can_advance():
    """Failed batches save verified siblings; immutable retry keys can gain work."""
    for workflow, job in (
        ("docs.yml", "exposition"),
        ("exposition-verify.yml", "verify"),
    ):
        steps = yaml.safe_load((WORKFLOWS / workflow).read_text())["jobs"][job]["steps"]
        names = {step.get("name"): step for step in steps}
        restored = names["Restore project extraction cache"]
        saved = names["Save project extraction cache"]
        assert saved["if"].startswith("always() &&")
        assert "steps.extraction-cache.outcome == 'success'" in saved["if"]
        assert (
            "${{ github.run_id }}-${{ github.run_attempt }}" in restored["with"]["key"]
        )
        assert "github.run_id" not in restored["with"]["restore-keys"]
        # Builder/UI/tests do not produce extraction records; their edits must
        # still verify minimal files without throwing away valid extraction.
        extraction_key = restored["with"]["key"]
        assert "scripts/exposition/**" not in extraction_key
        assert "scripts/exposition/build-minimal.mjs" not in extraction_key
        assert "scripts/exposition/Extract.lean" in extraction_key
        assert "scripts/exposition/extract-all.sh" in extraction_key


def test_minimal_build_wait_does_not_consume_verification_window() -> None:
    """A cold producer cannot use the verifier's six-hour execution allowance."""
    jobs = yaml.safe_load((WORKFLOWS / "exposition-verify.yml").read_text())["jobs"]
    assert jobs["verify"]["needs"] == ["scope", "build-ready"]
    waiting = jobs["build-ready"]
    assert waiting["needs"] == "scope"
    assert "needs.scope.outputs.applicable == 'true'" in waiting["if"]
    assert "github.event_name == 'pull_request'" in waiting["if"]
    commands = [step.get("run", "") for step in waiting["steps"]]
    assert any("lean_pool.ci_artifacts wait" in command for command in commands)
    assert any("--wait-seconds 18000" in command for command in commands)
    assert not any(
        "lake build" in command or "extract-all" in command for command in commands
    )
    guard = jobs["verify"]["steps"][0]
    for event, result, accepted in (
        ("pull_request", "success", True),
        ("pull_request", "failure", False),
        ("pull_request", "cancelled", False),
        ("pull_request", "skipped", False),
        ("pull_request", "", False),
        ("merge_group", "skipped", True),
        ("merge_group", "failure", False),
        ("schedule", "skipped", True),
        ("schedule", "failure", False),
        ("workflow_dispatch", "skipped", True),
        ("workflow_dispatch", "failure", False),
    ):
        process = subprocess.run(
            ["bash", "-e", "-c", guard["run"]],
            env={
                **os.environ,
                "SCOPE_RESULT": "success",
                "APPLICABLE": "true",
                "BUILD_READY_RESULT": result,
                "EVENT": event,
            },
            capture_output=True,
        )
        assert (process.returncode == 0) == accepted


@pytest.fixture
def scope_repository(tmp_path: Path) -> tuple[Path, str]:
    """Create a real diff for executing the workflow classifiers."""
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(
        ["git", "config", "core.quotePath", "true"], cwd=tmp_path, check=True
    )
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "--allow-empty",
            "-qm",
            "base",
        ],
        cwd=tmp_path,
        check=True,
    )
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
    ).strip()
    return tmp_path, base


@pytest.mark.parametrize("event", ["pull_request", "merge_group"])
@pytest.mark.parametrize(
    "filename,changed,expected",
    [
        ("docs.yml", "LeanPool/Example/Proof.lean", False),
        ("docs.yml", "LeanPool/projects/example.yaml", False),
        ("docs.yml", "README.md", False),
        ("docs.yml", "docbuild/lakefile.toml", True),
        ("docs.yml", "docbuild/名前.lean", True),
        ("docs.yml", "docbuild/line\nbreak.lean", True),
        ("docs.yml", "lean-toolchain", True),
        ("docs.yml", "lake-manifest.json", True),
        ("docs.yml", "python/lean_pool/exposition/generate.py", True),
        ("docs.yml", "scripts/exposition/extract-all.sh", True),
        ("docs.yml", ".github/workflows/docs.yml", True),
        ("workflow_lint.yml", "LeanPool/Example/Proof.lean", False),
        ("workflow_lint.yml", "python/lean_pool/ci_cache.py", False),
        ("workflow_lint.yml", ".github/workflows/cache-maintenance.yml", True),
        ("workflow_lint.yml", ".github/workflows/名前.yml", True),
        ("workflow_lint.yml", ".github/workflows/line\nbreak.yml", True),
    ],
)
def test_scoped_checks_classify_real_diffs(
    scope_repository, filename, changed, expected, event
) -> None:
    """Only relevant PR and queue changes allocate expensive validation jobs."""
    root, base = scope_repository
    path = root / changed
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("change\n")
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "change",
        ],
        cwd=root,
        check=True,
    )
    workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
    command = workflow["jobs"]["scope"]["steps"][-1]["run"]
    output = root / "output"
    subprocess.run(
        ["bash", "-e", "-c", command],
        cwd=root,
        check=True,
        env={**os.environ, "EVENT": event, "BASE": base, "GITHUB_OUTPUT": str(output)},
    )
    assert output.read_text().strip() == f"applicable={str(expected).lower()}"


@pytest.mark.parametrize("event", ["pull_request", "merge_group"])
@pytest.mark.parametrize(
    "filename,original",
    [
        ("docs.yml", "docbuild/lean-toolchain"),
        ("workflow_lint.yml", ".github/workflows/example.yml"),
    ],
)
def test_moving_files_out_of_scope_still_runs_validation(
    scope_repository, filename, original, event
):
    """Renaming a configuration outside its directory must validate its removal."""
    root, _ = scope_repository
    base = _move_scope_file(root, original)
    workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
    output = root / "output"
    subprocess.run(
        ["bash", "-e", "-c", workflow["jobs"]["scope"]["steps"][-1]["run"]],
        cwd=root,
        check=True,
        env={**os.environ, "EVENT": event, "BASE": base, "GITHUB_OUTPUT": str(output)},
    )
    assert output.read_text().strip() == "applicable=true"
    if filename == "docs.yml" and event == "pull_request":
        detection = next(
            step
            for step in workflow["jobs"]["preflight"]["steps"]
            if step.get("name") == "Detect README-only change"
        )
        output.write_text("")
        subprocess.run(
            ["bash", "-e", "-c", detection["run"]],
            cwd=root,
            check=True,
            env={
                **os.environ,
                "EVENT_NAME": event,
                "BASE_SHA": base,
                "HEAD_SHA": "HEAD",
                "GITHUB_OUTPUT": str(output),
            },
        )
        assert output.read_text().strip() == "readme_only=false"


def _scope_commit(root: Path) -> None:
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "configuration change",
        ],
        cwd=root,
        check=True,
    )


def _move_scope_file(root: Path, original: str) -> str:
    path = root / original
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("original configuration\n")
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    _scope_commit(root)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    path.rename(root / "README.md")
    subprocess.run(["git", "add", "-A"], cwd=root, check=True)
    _scope_commit(root)
    return base


@pytest.mark.parametrize("event", ["pull_request", "merge_group", "push"])
def test_lean_planner_retains_removed_configuration_after_rename(
    scope_repository, event
):
    """A renamed toolchain remains a build and dependency-test input."""
    root, _ = scope_repository
    base = _move_scope_file(root, "lean-toolchain")
    jobs = yaml.safe_load((WORKFLOWS / "lean_action_ci.yml").read_text())["jobs"]
    planning = next(step for step in jobs["plan"]["steps"] if step.get("id") == "plan")
    command = (
        'case "$EVENT_NAME" in'
        + planning["run"].split('case "$EVENT_NAME" in', 1)[1].split("esac", 1)[0]
        + "esac"
    )
    changed_files = root / "changed"
    subprocess.run(
        ["bash", "-e", "-c", command],
        cwd=root,
        check=True,
        env={
            **os.environ,
            "EVENT_NAME": event,
            "BASE_SHA": base,
            "BEFORE_SHA": base,
            "changed_files": str(changed_files),
        },
    )
    assert set(changed_files.read_text().splitlines()) == {
        "README.md",
        "lean-toolchain",
    }
    command = (
        "dependency_tests=true"
        + planning["run"].split("dependency_tests=true", 1)[1].split("cold=false", 1)[0]
    )
    output = root / "output"
    subprocess.run(
        ["bash", "-e", "-c", command],
        cwd=root,
        check=True,
        env={
            **os.environ,
            "changed_files": str(changed_files),
            "diff_available": "true",
            "FORCE_FULL": "false",
            "GITHUB_OUTPUT": str(output),
        },
    )
    assert output.read_text().strip() == "dependency_tests=true"


@pytest.mark.parametrize("filename", ["docs.yml", "workflow_lint.yml"])
def test_scoped_checks_do_not_skip_when_git_diff_fails(scope_repository, filename):
    """An unavailable base produces failure rather than a false skip decision."""
    root, _ = scope_repository
    workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
    command = workflow["jobs"]["scope"]["steps"][-1]["run"]
    output = root / "output"
    process = subprocess.run(
        ["bash", "-e", "-c", command],
        cwd=root,
        capture_output=True,
        env={
            **os.environ,
            "EVENT": "pull_request",
            "BASE": "missing-base",
            "GITHUB_OUTPUT": str(output),
        },
    )
    assert process.returncode != 0
    assert not output.exists()


@pytest.mark.parametrize("filename", ["docs.yml", "workflow_lint.yml"])
@pytest.mark.parametrize("event", ["push", "workflow_dispatch"])
def test_scoped_checks_run_for_main_and_manual_requests(tmp_path, filename, event):
    """Publishing and explicit requests retain validation without needing a diff."""
    workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
    command = workflow["jobs"]["scope"]["steps"][-1]["run"]
    output = tmp_path / "output"
    subprocess.run(
        ["bash", "-e", "-c", command],
        cwd=tmp_path,
        check=True,
        env={
            **os.environ,
            "EVENT": event,
            "BASE": "missing-base",
            "GITHUB_OUTPUT": str(output),
        },
    )
    assert output.read_text().strip() == "applicable=true"


@pytest.mark.parametrize("filename", ["docs.yml", "workflow_lint.yml"])
def test_scoped_checks_handle_large_diffs(tmp_path, filename):
    """An early match cannot become a false skip through a broken shell pipe."""
    commands = tmp_path / "commands"
    commands.mkdir()
    git = commands / "git"
    git.write_text('#!/bin/bash\ncat "$CHANGED_FILES"\n')
    git.chmod(0o755)
    changed_files = tmp_path / "changed"
    changed_files.write_text(
        ".github/workflows/docs.yml\n"
        + "LeanPool/Example/LongPath/Proof.lean\n" * 10000
    )
    workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
    command = workflow["jobs"]["scope"]["steps"][-1]["run"]
    output = tmp_path / "output"
    subprocess.run(
        ["bash", "-e", "-c", command],
        cwd=tmp_path,
        check=True,
        env={
            **os.environ,
            "PATH": f"{commands}:{os.environ['PATH']}",
            "EVENT": "pull_request",
            "BASE": "base",
            "CHANGED_FILES": str(changed_files),
            "GITHUB_OUTPUT": str(output),
        },
    )
    assert output.read_text().strip() == "applicable=true"


@pytest.mark.parametrize(
    "changed,diff_available,force_full,expected",
    [
        ("LeanPool/Example/Proof.lean", "true", "false", False),
        ("LeanPool/projects/example.yaml", "true", "false", False),
        ("lean-toolchain", "true", "false", True),
        ("lakefile.toml", "true", "false", True),
        ("lake-manifest.json", "true", "false", True),
        ("python/lean_pool/ci_pr_build.py", "true", "false", True),
        ("python/tests/test_ci_pr_build.py", "true", "false", True),
        ('"python/lean_pool/quoted.py"', "true", "false", True),
        ("scripts/ProjectIndexes.lean", "true", "false", True),
        (".github/workflows/lean_action_ci.yml", "true", "false", True),
        ("", "false", "false", True),
        ("LeanPool/Example/Proof.lean", "true", "true", True),
    ],
)
def test_dependency_tracking_tests_scope(
    tmp_path, changed, diff_available, force_full, expected
):
    """Dependency tracking is tested for tooling changes and unknown/manual scopes."""
    jobs = yaml.safe_load((WORKFLOWS / "lean_action_ci.yml").read_text())["jobs"]
    planning = next(step for step in jobs["plan"]["steps"] if step.get("id") == "plan")
    command = (
        "dependency_tests=true"
        + planning["run"].split("dependency_tests=true", 1)[1].split("cold=false", 1)[0]
    )
    changed_files = tmp_path / "changed"
    changed_files.write_text(changed + "\n")
    output = tmp_path / "output"
    subprocess.run(
        ["bash", "-e", "-c", command],
        check=True,
        env={
            **os.environ,
            "changed_files": str(changed_files),
            "diff_available": diff_available,
            "FORCE_FULL": force_full,
            "GITHUB_OUTPUT": str(output),
        },
    )
    assert output.read_text().strip() == f"dependency_tests={str(expected).lower()}"
    for name in ("build", "finalize", "rebase"):
        tracking = next(
            step
            for step in jobs[name]["steps"]
            if step.get("name")
            == "Check compiled artifact dependency tracking with pinned Lean"
        )
        assert tracking["if"] == "needs.plan.outputs.dependency_tests == 'true'"


def test_profiling_is_opt_in_and_cache_pruning_is_scheduled() -> None:
    """Advisory compilation and maintenance do not run on ordinary PR events."""
    profiling = yaml.safe_load((WORKFLOWS / "proof-profile.yml").read_text())
    assert set(profiling.get("on", profiling.get(True))) == {
        "issue_comment",
        "workflow_dispatch",
    }
    maintenance = yaml.safe_load((WORKFLOWS / "cache-maintenance.yml").read_text())
    assert set(maintenance.get("on", maintenance.get(True))) == {
        "schedule",
        "workflow_dispatch",
    }
    assert maintenance["permissions"]["actions"] == "write"
    for filename in ("lean_action_ci.yml", "docs.yml"):
        workflow = yaml.safe_load((WORKFLOWS / filename).read_text())
        assert not any(
            "lean_pool.ci_cache prune" in step.get("run", "")
            for job in workflow["jobs"].values()
            for step in job["steps"]
        )
