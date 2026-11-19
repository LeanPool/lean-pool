"""Keep the linter plugin built before any CI build that names modules one by one.

Every pool module loads the `LeanPoolLinters` plugin. Asked for thousands of
module targets in one command, Lake (v4.35.0 and v4.36.0) starts several jobs
for that one plugin instead of sharing one. They write the same response file
and library, and a job whose response file another has already removed fails
with "no such file or directory" or "clang: error: no input files". A restored
build output hides this, so it appears when the toolchain or the plugin
changes: two of the fourteen shards of the v4.36.0 migration failed this way.

`lake build LeanPool`, one library target, shares the plugin job and needs no
such step.
"""

from __future__ import annotations

import re
from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[2] / ".github/workflows/lean_action_ci.yml"
PLUGIN = "lake build LeanPoolLinters:shared"
# A build whose targets come from a shell variable: a list of modules.
MODULE_LIST_BUILD = re.compile(r"lake build \$")


def module_list_builds() -> list[tuple[str, str]]:
    """Return the job and script of every step that builds a list of modules."""
    workflow = yaml.safe_load(WORKFLOW.read_text())
    return [
        (name, step["run"])
        for name, job in workflow["jobs"].items()
        for step in job.get("steps", [])
        if MODULE_LIST_BUILD.search(step.get("run", ""))
    ]


def test_module_list_builds_link_the_plugin_first() -> None:
    """A shard build links the plugin alone before it asks for its modules."""
    builds = module_list_builds()
    assert [job for job, _ in builds] == ["shard"]
    for job, script in builds:
        build = MODULE_LIST_BUILD.search(script)
        assert build is not None
        assert PLUGIN in script[: build.start()], job


def test_plugin_target_is_the_one_the_pool_loads() -> None:
    """The step builds the very target that `lakefile.toml` names as the plugin."""
    lakefile = (WORKFLOW.parents[2] / "lakefile.toml").read_text()
    assert f'plugins = ["{PLUGIN.removeprefix("lake build ")}"]' in lakefile
