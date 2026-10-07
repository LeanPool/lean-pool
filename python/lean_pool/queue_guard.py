"""Apply the content separation policy to each PR's commit in a merge group."""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

BUMP_METADATA = {
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "docbuild/lean-toolchain",
    "docbuild/lakefile.toml",
    "docbuild/lake-manifest.json",
    ".github/workflows/content-pr-guard.yml",
}


def is_content(path: str) -> bool:
    """Identify proof sources and their per-project metadata."""
    return bool(re.fullmatch(r"LeanPool/projects/[A-Za-z0-9_-]+\.yaml", path)) or (
        path.startswith("LeanPool/") and path.endswith(".lean")
    )


def separation_errors(paths: list[str], *, legacy: bool = False) -> list[str]:
    """Retain the existing version-bump exception without permitting mixed PRs."""
    if "LeanPool.lean" in paths and not legacy:
        return ["LeanPool.lean is fixed; content PRs must not edit it"]
    content = [
        path
        for path in paths
        if is_content(path)
        or (legacy and path in {"LeanPool.lean", "LeanPool/projects.yml"})
    ]
    other = set(paths) - set(content)
    if content and other - BUMP_METADATA:
        return sorted(other - BUMP_METADATA)
    return []


def group_changes(root: Path, base: str, head: str) -> list[list[str]]:
    """Read separate squash commits so unrelated PRs are never graded as one PR."""

    def git(*arguments: str) -> str:
        return subprocess.check_output(["git", *arguments], cwd=root, text=True)

    git("merge-base", "--is-ancestor", base, head)
    commits = git("rev-list", "--reverse", f"{base}..{head}").splitlines()
    if not commits:
        raise ValueError("merge group contains no commits")
    result = []
    for commit in commits:
        if len(git("rev-list", "--parents", "-n", "1", commit).split()) != 2:
            raise ValueError("merge queue must use squash commits")
        result.append(
            git("diff", "--name-only", "-z", f"{commit}^", commit)
            .strip("\0")
            .split("\0")
        )
    return result


def main() -> None:
    """Fail the queue gate if any constituent PR violates separation."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    arguments = parser.parse_args()
    legacy = (
        subprocess.run(
            ["git", "cat-file", "-e", f"{arguments.base}:LeanPool/projects.yml"],
            capture_output=True,
            check=False,
        ).returncode
        == 0
    )
    for paths in group_changes(Path.cwd(), arguments.base, arguments.head):
        errors = separation_errors(paths, legacy=legacy)
        if errors:
            raise SystemExit("Content separation failed: " + ", ".join(errors))
    print("Every queued PR preserves content separation")


if __name__ == "__main__":
    main()
