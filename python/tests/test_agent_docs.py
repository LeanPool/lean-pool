"""The instructions agents read must be the current README and contributing guide."""

from __future__ import annotations

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
HEADER = "This file is a concatenation of README.md and CONTRIBUTING.md.\n"


def generated() -> str:
    """What ``make agent-docs`` writes."""
    readme = (ROOT / "README.md").read_text()
    contributing = (ROOT / "CONTRIBUTING.md").read_text()
    return f"{HEADER}\n{readme}\n{contributing}"


@pytest.mark.parametrize("name", ["AGENTS.md", "CLAUDE.md"])
def test_agent_instructions_match_their_sources(name: str) -> None:
    """A stale copy gives every automated worker outdated rules."""
    assert (ROOT / name).read_text() == generated(), (
        f"{name} is out of date; run `make agent-docs` and commit the result"
    )


def test_the_daily_refresh_regenerates_the_copies() -> None:
    """The README statistics change daily on main, outside any pull request."""
    workflow = (ROOT / ".github" / "workflows" / "docs-publish.yml").read_text()
    rest = workflow.split("- name: Commit generated metadata", 1)[1]
    step = re.split(r"\n  \S", rest, maxsplit=1)[0]
    generators = step.index("lean_pool.notice")
    regenerate = step.index("make agent-docs")
    commit = step.index("git add README.md NOTICE AGENTS.md CLAUDE.md")
    assert generators < regenerate < commit
