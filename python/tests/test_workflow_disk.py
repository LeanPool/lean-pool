"""Coverage for the free-disk-before-pool-restore workflow check."""

from pathlib import Path

import yaml

from lean_pool.workflow_disk import ACTION_PATH, workflow_errors

REPOSITORY = Path(__file__).resolve().parents[2]
SCRIPT = "sudo rm -rf /usr/share/dotnet /usr/local/lib/android\ndf -h /\n"
CHECKOUT = {"uses": "actions/checkout@sha"}
FREE = {"name": "Free runner disk space", "uses": "./.github/actions/free-disk-space"}
RESTORE = {
    "name": "Restore pool build",
    "uses": "actions/cache/restore@sha",
    "with": {"path": ".lake/build", "key": "LeanPoolBuild-v1-Linux-abc"},
}


def write_repository(root: Path, steps: list[dict]) -> Path:
    """Create a repository with the shared action and one single-job workflow."""
    action = root / ACTION_PATH
    action.parent.mkdir(parents=True)
    action.write_text(
        yaml.safe_dump(
            {"runs": {"using": "composite", "steps": [{"run": SCRIPT}]}},
        )
    )
    workflows = root / ".github/workflows"
    workflows.mkdir(parents=True)
    (workflows / "build.yml").write_text(
        yaml.safe_dump({"jobs": {"build": {"steps": steps}}})
    )
    return root


def test_repository_workflows_free_disk_before_pool_restore():
    """Every real workflow passes, so the gate starts green."""
    assert workflow_errors(REPOSITORY) == []


def test_restore_without_cleanup_fails(tmp_path):
    """A job that restores the pool build without cleanup is reported."""
    errors = workflow_errors(write_repository(tmp_path, [CHECKOUT, RESTORE]))
    assert len(errors) == 1
    assert "without an earlier cleanup" in errors[0]


def test_cleanup_after_restore_fails(tmp_path):
    """Cleanup must come before the restore, not after it."""
    errors = workflow_errors(write_repository(tmp_path, [CHECKOUT, RESTORE, FREE]))
    assert len(errors) == 1


def test_shared_action_or_exact_inline_copy_passes(tmp_path):
    """Both the shared action and an identical inline script are accepted."""
    inline = {"name": "Free runner disk space", "run": SCRIPT}
    assert workflow_errors(write_repository(tmp_path / "a", [FREE, RESTORE])) == []
    assert workflow_errors(write_repository(tmp_path / "b", [inline, RESTORE])) == []


def test_drifted_inline_copy_fails(tmp_path):
    """An inline cleanup that no longer matches the shared action is reported."""
    drifted = {"run": "sudo rm -rf /usr/share/dotnet\ndf -h /\n"}
    errors = workflow_errors(write_repository(tmp_path, [drifted, RESTORE]))
    assert any("differs from" in error for error in errors)


def test_lookup_only_and_other_caches_are_exempt(tmp_path):
    """Lookups download nothing, and the dependency cache alone fits on disk."""
    lookup = {**RESTORE, "with": {**RESTORE["with"], "lookup-only": True}}
    dependencies = {
        "uses": "actions/cache/restore@sha",
        "with": {"path": ".lake/packages", "key": "LeanDependencies-v1-Linux-abc"},
    }
    root = write_repository(tmp_path, [CHECKOUT, lookup, dependencies])
    assert workflow_errors(root) == []


def test_conditional_cleanup_does_not_cover_unconditional_restore(tmp_path):
    """Cleanup skipped on some events leaves those restores unprotected."""
    conditional = {**FREE, "if": "github.event_name == 'push'"}
    errors = workflow_errors(write_repository(tmp_path, [conditional, RESTORE]))
    assert len(errors) == 1


def test_cleanup_with_the_restores_condition_passes(tmp_path):
    """A cleanup gated exactly like its restore always runs alongside it."""
    condition = "github.event_name == 'push'"
    steps = [{**FREE, "if": condition}, {**RESTORE, "if": condition}]
    assert workflow_errors(write_repository(tmp_path, steps)) == []


def test_pool_build_fallback_key_counts_as_a_restore(tmp_path):
    """A pool build restored through `restore-keys` still needs cleanup."""
    fallback = {
        **RESTORE,
        "with": {
            "path": ".lake/build",
            "key": "Other-v1-abc",
            "restore-keys": "LeanPoolBuild-v1-Linux-\n",
        },
    }
    errors = workflow_errors(write_repository(tmp_path, [CHECKOUT, fallback]))
    assert len(errors) == 1


def test_save_only_steps_are_exempt(tmp_path):
    """Saving uploads the build; it downloads nothing onto the runner."""
    save = {**RESTORE, "uses": "actions/cache/save@sha"}
    assert workflow_errors(write_repository(tmp_path, [CHECKOUT, save])) == []


def test_every_restore_is_checked_not_only_the_first(tmp_path):
    """A covered conditional restore does not excuse a later unconditional one."""
    condition = "github.event_name == 'push'"
    steps = [{**FREE, "if": condition}, {**RESTORE, "if": condition}, RESTORE]
    errors = workflow_errors(write_repository(tmp_path, steps))
    assert len(errors) == 1
