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
    assert "restores the pool build cache before freeing disk" in errors[0]


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
