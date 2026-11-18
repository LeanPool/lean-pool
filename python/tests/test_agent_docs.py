"""The instructions agents read must be the current README and contributing guide."""

from __future__ import annotations

import fnmatch
import re
from pathlib import Path

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = ROOT / ".github" / "workflows"
HEADER = "This file is a concatenation of README.md and CONTRIBUTING.md.\n"
# What the tests in this directory read outside ``python/``.
TEST_INPUTS = (
    "README.md",
    "CONTRIBUTING.md",
    "AGENTS.md",
    "CLAUDE.md",
    "Makefile",
    *(f".github/workflows/{path.name}" for path in sorted(WORKFLOWS.glob("*.yml"))),
)


def generated() -> str:
    """What ``make agent-docs`` writes."""
    readme = (ROOT / "README.md").read_text()
    contributing = (ROOT / "CONTRIBUTING.md").read_text()
    return f"{HEADER}\n{readme}\n{contributing}"


def commands(script: str) -> list[str]:
    """The lines of a shell script that run, without comments or indentation."""
    lines = (line.strip() for line in script.splitlines())
    return [line for line in lines if line and not line.startswith("#")]


@pytest.mark.parametrize("name", ["AGENTS.md", "CLAUDE.md"])
def test_agent_instructions_match_their_sources(name: str) -> None:
    """A stale copy gives every automated worker outdated rules."""
    assert (ROOT / name).read_text() == generated(), (
        f"{name} is out of date; run `make agent-docs` and commit the result"
    )


def test_the_generator_writes_what_the_test_expects() -> None:
    """The comparison above is only as good as its model of the Makefile."""
    recipe = (ROOT / "Makefile").read_text().split("agent-docs:\n", 1)[1]
    recipe = recipe.split("\n\n", 1)[0]
    assert commands(recipe.replace("\t@", "")) == [
        f'echo "{HEADER.strip()}" > CLAUDE.md',
        'echo "" >> CLAUDE.md',
        "cat README.md >> CLAUDE.md",
        'echo "" >> CLAUDE.md',
        "cat CONTRIBUTING.md >> CLAUDE.md",
        "cp CLAUDE.md AGENTS.md",
        'echo "Generated CLAUDE.md and AGENTS.md"',
    ]


def test_the_daily_refresh_regenerates_and_commits_the_copies() -> None:
    """The README statistics change daily on main, outside any pull request."""
    publisher = yaml.safe_load((WORKFLOWS / "docs-publish.yml").read_text())
    steps = [
        step
        for job in publisher["jobs"].values()
        for step in job.get("steps", [])
        if step.get("name") == "Commit generated metadata"
    ]
    assert len(steps) == 1
    script = commands(steps[0]["run"])
    positions = [
        script.index("(cd python && uv run python -m lean_pool.stats --repo ..)"),
        script.index("(cd python && uv run python -m lean_pool.notice --repo ..)"),
        script.index("make agent-docs"),
        next(i for i, line in enumerate(script) if line.startswith("unexpected=")),
        script.index("git add README.md NOTICE AGENTS.md CLAUDE.md"),
        next(i for i, line in enumerate(script) if line.startswith("git commit ")),
    ]
    assert positions == sorted(positions)
    allowed = re.search(r"grep -vE '([^']+)'", script[positions[3]])
    assert allowed is not None
    for name in ("NOTICE", "README.md", "AGENTS.md", "CLAUDE.md"):
        assert re.fullmatch(allowed.group(1), name), name
    assert not re.fullmatch(allowed.group(1), "lakefile.toml")


@pytest.mark.parametrize("path", TEST_INPUTS)
def test_python_ci_runs_when_a_test_input_changes(path: str) -> None:
    """A change that only touches what a test reads must still run the tests."""
    workflow = yaml.safe_load((WORKFLOWS / "python_ci.yml").read_text())
    # PyYAML reads the key ``on`` as the boolean True.
    pushes = workflow[True]["push"]["paths"]
    assert any(fnmatch.fnmatch(path, pattern) for pattern in pushes), path
    scope = next(
        step["run"]
        for step in workflow["jobs"]["scope"]["steps"]
        if step.get("id") == "scope"
    )
    selector = re.search(r"grep -Eq '([^']+)'", scope)
    assert selector is not None
    assert re.search(selector.group(1), path), path


def test_python_ci_still_skips_content_only_changes() -> None:
    """Imports and proof optimizations do not need the Python suite."""
    workflow = yaml.safe_load((WORKFLOWS / "python_ci.yml").read_text())
    scope = next(
        step["run"]
        for step in workflow["jobs"]["scope"]["steps"]
        if step.get("id") == "scope"
    )
    selector = re.search(r"grep -Eq '([^']+)'", scope).group(1)
    for path in ("LeanPool/Example/Basic.lean", "LeanPool/projects/example.yaml"):
        assert not re.search(selector, path), path
