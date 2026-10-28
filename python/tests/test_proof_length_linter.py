"""Exercise the proof-length plugin through Lake with the pinned Lean compiler."""

from __future__ import annotations

import os
import runpy
import shutil
import subprocess
import tomllib
from pathlib import Path

import pytest
import yaml


def _pinned_lake(root: Path) -> Path:
    """Find the pinned Lake executable, failing in CI if it is unavailable."""
    pin = (root / "lean-toolchain").read_text().strip()
    lake = (
        Path.home()
        / ".elan/toolchains"
        / pin.replace("/", "--").replace(":", "---")
        / "bin/lake"
    )
    if not lake.is_file():
        if os.environ.get("LEAN_POOL_REQUIRE_TEST_TOOLCHAIN") == "1":
            pytest.fail("required pinned Lean toolchain unavailable")
        pytest.skip("pinned Lean toolchain unavailable")
    return lake


def _write_test_project(root: Path, destination: Path) -> None:
    """Create a dependency-free project that loads the plugin without imports."""
    shutil.copyfile(root / "lean-toolchain", destination / "lean-toolchain")
    (destination / "lakefile.toml").write_text(
        'name = "proof_length_test"\n'
        '[[lean_lib]]\nname = "LeanPoolLinters"\nsrcDir = "scripts/ci"\n'
        '[[lean_lib]]\nname = "LeanPool"\n'
        'roots = ["LeanPool", "DefaultBoundary"]\n'
        'plugins = ["LeanPoolLinters:shared"]\n'
    )
    plugin = destination / "scripts/ci/LeanPoolLinters.lean"
    plugin.parent.mkdir(parents=True)
    shutil.copyfile(root / "scripts/ci/LeanPoolLinters.lean", plugin)
    fixtures = (root / "scripts/ci/LeanPoolLintersTest.lean").read_text()
    assert "import LeanPoolLinters" not in fixtures
    # Also emit a real, unguarded warning so CI's ordinary warning gate can see it.
    consumer = destination / "LeanPool.lean"
    consumer.write_text(
        fixtures + "\ntheorem unguardedLongProof : True := by\n"
        "  skip\n  skip\n  exact True.intro\n"
    )


def _write_default_boundary_fixture(destination: Path) -> None:
    """Generate proofs exactly at and one line above the production limit."""
    # Exercise the actual production default, not just the fixtures' small bound.
    # The guarded proof has 200 lines; its unguarded neighbour has 201.
    (destination / "DefaultBoundary.lean").write_text(
        "".join(
            [
                "module\nimport Lean.Elab.GuardMsgs\n\n#guard_msgs in\n",
                "theorem exactlyAtDefaultLimit : True := by\n",
                "  skip\n" * 198,
                "  exact True.intro\n\n",
                "theorem exceedingDefaultLimit : True := by\n",
                "  skip\n" * 199,
                "  exact True.intro\n",
            ]
        )
    )


def test_lake_proof_length_plugin(tmp_path: Path) -> None:
    """Load the plugin without source imports and check its source-range fixtures."""
    root = Path(__file__).resolve().parents[2]
    lake = _pinned_lake(root)
    configuration = tomllib.loads((root / "lakefile.toml").read_text())
    libraries = {library["name"]: library for library in configuration["lean_lib"]}
    assert libraries["LeanPool"]["plugins"] == ["LeanPoolLinters:shared"]
    assert libraries["LeanPoolLinters"]["srcDir"] == "scripts/ci"
    _write_test_project(root, tmp_path)
    _write_default_boundary_fixture(tmp_path)
    result = subprocess.run(
        [str(lake), "build", "LeanPool"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=180,
    )
    output = result.stdout + result.stderr
    assert result.returncode == 0, output
    assert "warning: LeanPool.lean:" in output, output
    assert output.count("This proof contains 4 non-comment lines") == 1, output
    assert "exceeding the limit of 3" in output, output
    assert output.count("This proof contains 201 non-comment lines") == 1, output
    assert "exceeding the limit of 200" in output, output
    assert "error:" not in output, output


def test_proof_length_plugin_invalidates_build_shards() -> None:
    """A plugin-only edit must rebuild all projects, not just reuse old results."""
    root = Path(__file__).resolve().parents[2]
    planner = runpy.run_path(str(root / "scripts/ci/plan-build-shards.py"))
    assert "scripts/ci/LeanPoolLinters.lean" in planner["GLOBAL_BUILD_INPUTS"]


def test_proof_length_plugin_has_pinned_ci_coverage() -> None:
    """Run the fixture in Lean-equipped CI, rather than skipping it in Python CI."""
    root = Path(__file__).resolve().parents[2]
    workflow = yaml.safe_load(
        (root / ".github/workflows/lean_action_ci.yml").read_text()
    )
    steps = [
        step
        for job in workflow["jobs"].values()
        for step in job.get("steps", [])
        if "python/tests/test_proof_length_linter.py" in step.get("run", "")
    ]
    assert len(steps) == 3
    for step in steps:
        assert step["env"]["LEAN_POOL_REQUIRE_TEST_TOOLCHAIN"] == "1"
        assert "-k 'test_lake_'" in step["run"]
