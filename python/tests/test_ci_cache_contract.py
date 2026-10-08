"""Keep shared cache producers and consumers compatible across CI workflows."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

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
    """A PR runs its protected preflight without allocating heavy docs runners."""
    jobs = yaml.safe_load((WORKFLOWS / "docs.yml").read_text())["jobs"]
    assert jobs["preflight"]["name"] == "Documentation preflight"
    assert "if" not in jobs["preflight"]
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
        + planning["run"].split("minimal_build=false", 1)[1].split("cold=false", 1)[0]
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
