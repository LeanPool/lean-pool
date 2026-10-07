"""Read per-project cards consistently, including historical monolithic registries."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections.abc import Callable
from pathlib import Path
from typing import Any

import yaml

DIRECTORY = "LeanPool/projects"
LEGACY = "LeanPool/projects.yml"
CARD_NAME = re.compile(r"[A-Za-z0-9_-]+\.yaml\Z")


def card_path(path: str) -> bool:
    """Recognize a single card, excluding nested or arbitrary registry files."""
    parent, _, name = path.rpartition("/")
    return parent == DIRECTORY and CARD_NAME.fullmatch(name) is not None


def combine(cards: dict[str, str]) -> dict[str, Any]:
    """Validate the file container and preserve all fields for existing validators."""
    projects = []
    for name, text in sorted(cards.items()):
        if not CARD_NAME.fullmatch(name):
            raise ValueError(f"unexpected registry file: {name}")
        data = yaml.load(text, Loader=_UniqueLoader)
        if not isinstance(data, dict):
            raise ValueError(f"{name}: project card must contain a mapping")
        if data.get("slug") != name.removesuffix(".yaml"):
            raise ValueError(f"{name}: filename must match the project slug")
        projects.append(data)
    if not projects:
        raise ValueError("project registry contains no cards")
    return {"projects": projects}


def load_document(path: Path) -> Any:
    """Read a registry directory or an old file, rejecting ambiguous mixed layouts."""
    directory = path if path.is_dir() else path.parent / "projects"
    if directory.is_dir():
        if directory.is_symlink():
            raise ValueError("registry directory must not be a symbolic link")
        if (directory.parent / "projects.yml").exists():
            raise ValueError("both registry directory and legacy registry exist")
        entries = list(directory.iterdir())
        if any(p.is_symlink() or not p.is_file() for p in entries):
            raise ValueError("registry must contain ordinary project card files only")
        return combine({p.name: p.read_text() for p in entries})
    if not path.is_file():
        raise FileNotFoundError(path)
    return yaml.safe_load(path.read_text()) or {}


def read_revision(root: Path, revision: str) -> dict[str, Any]:
    """Read cards from immutable Git objects without checking out a branch."""

    def git(*arguments: str) -> str:
        return subprocess.check_output(["git", *arguments], cwd=root, text=True)

    entries = git("ls-tree", "-r", revision, "--", DIRECTORY).splitlines()
    paths = []
    for entry in entries:
        metadata, name = entry.split("\t", 1)
        if metadata.split()[:2] != ["100644", "blob"] or not card_path(name):
            raise ValueError("unexpected registry path or file type")
        paths.append(name)
    if paths:
        if (
            subprocess.run(
                ["git", "cat-file", "-e", f"{revision}:{LEGACY}"],
                cwd=root,
                capture_output=True,
                check=False,
            ).returncode
            == 0
        ):
            raise ValueError("both registry layouts exist at revision")
        if not all(card_path(path) for path in paths):
            raise ValueError("unexpected registry path")
        return combine(
            {Path(path).name: git("show", f"{revision}:{path}") for path in paths}
        )
    return yaml.safe_load(git("show", f"{revision}:{LEGACY}")) or {}


def remote_text(
    repository: str, revision: str, fetch: Callable[[str, str, str], str | None]
) -> str | None:
    """Assemble remote cards for readers that compare complete YAML documents."""
    legacy = fetch(repository, LEGACY, revision)
    if legacy is not None:
        return legacy
    raw = subprocess.check_output(
        ["gh", "api", f"repos/{repository}/git/trees/{revision}?recursive=1"],
        text=True,
        timeout=60,
    )
    tree = json.loads(raw)
    if tree.get("truncated"):
        raise ValueError("GitHub registry tree is incomplete")
    entries = [
        item
        for item in tree["tree"]
        if item["path"].startswith(DIRECTORY + "/") and item["type"] != "tree"
    ]
    if any(
        not card_path(item["path"]) or item.get("mode") != "100644" for item in entries
    ):
        raise ValueError("unexpected remote registry file")
    paths = [item["path"] for item in entries]
    cards = {}
    for path in paths:
        text = fetch(repository, path, revision)
        if text is None:
            raise ValueError(f"could not read project card {path}")
        cards[Path(path).name] = text
    return yaml.safe_dump(combine(cards), sort_keys=False)


class _UniqueLoader(yaml.SafeLoader):
    """Reject repeated field names instead of silently losing card metadata."""

    def construct_mapping(self, node: Any, deep: bool = False) -> dict:
        result = {}
        for key_node, value_node in node.value:
            key = self.construct_object(key_node, deep=deep)
            if key in result:
                raise ValueError(f"duplicate YAML field: {key}")
            result[key] = self.construct_object(value_node, deep=deep)
        return result


def main() -> None:
    """Expose the same complete registry to shell importers and inspection tools."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--sources", action="store_true")
    arguments = parser.parse_args()
    document = load_document(arguments.repo / LEGACY)
    if arguments.sources:
        for card in document.get("projects", []):
            source = card.get("source", {}).get("github_repo")
            if source:
                print(source)
    else:
        print(yaml.safe_dump(document, sort_keys=False), end="")


if __name__ == "__main__":
    main()
