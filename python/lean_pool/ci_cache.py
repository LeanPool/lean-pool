"""Identify reusable Lean builds and bound saved main-branch cache copies."""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import subprocess
from pathlib import Path
from typing import Any

LOGGER = logging.getLogger(__name__)
CACHE_PREFIXES = (
    "LeanPoolBuild-v1-",
    "LeanDependencies-v1-",
    "LeanValidation-v1-",
    "DocsInfo-v3-",
    "DocsInfoMathlib-v3-",
    "Exposition-v1-",
)


def build_revision(root: Path, reference: str = "HEAD") -> str:
    """Identify tracked Lean sources and build scripts independently of commit IDs."""
    sources = subprocess.check_output(
        [
            "git",
            "ls-tree",
            "-r",
            "-z",
            reference,
            "--",
            "LeanPool",
            "LeanPool.lean",
            "scripts/ProjectIndexes.lean",
        ],
        cwd=root,
    )
    sources = b"\0".join(
        entry
        for entry in sources.split(b"\0")
        if entry.rsplit(b"\t", 1)[-1].endswith(b".lean")
    )
    if not sources:
        raise ValueError("no Lean build sources found")
    return hashlib.sha256(sources).hexdigest()


def cache_family(key: str) -> str:
    """Limit retention to one known cache kind on one runner operating system."""
    for prefix in CACHE_PREFIXES:
        if key.startswith(prefix):
            operating_system, separator, identity = key[len(prefix) :].partition("-")
            if operating_system and separator and identity:
                return prefix + operating_system + "-"
    raise ValueError(f"unsupported cache key: {key}")


def obsolete_caches(caches: list[dict[str, Any]], key: str) -> list[int]:
    """Prune old copies only after the replacement is visible on main."""
    family = cache_family(key)
    replacements = [
        cache
        for cache in caches
        if cache.get("ref") == "refs/heads/main" and cache.get("key") == key
    ]
    if not replacements:
        return []
    created = replacements[0].get("created_at", "")
    return [
        cache["id"]
        for cache in caches
        if cache.get("ref") == "refs/heads/main"
        and isinstance(cache.get("key"), str)
        and cache["key"].startswith(family)
        and cache["key"] != key
        and (not created or cache.get("created_at", "") < created)
    ]


def obsolete_main_caches(caches: list[dict[str, Any]]) -> list[int]:
    """Retain the newest main cache per known family and operating system."""
    newest: dict[str, dict[str, Any]] = {}
    for cache in caches:
        if cache.get("ref") != "refs/heads/main" or not cache.get("created_at"):
            continue
        try:
            family = cache_family(cache.get("key", ""))
        except ValueError:
            continue
        previous = newest.get(family)
        if previous is None or cache["created_at"] > previous["created_at"]:
            newest[family] = cache
    return sorted(
        {
            identifier
            for cache in newest.values()
            for identifier in obsolete_caches(caches, cache["key"])
        }
    )


def prune_cache(repository: str, key: str | None = None) -> None:
    """Remove older main caches after a specific or the newest replacement."""
    if key is not None:
        cache_family(key)
    pages = json.loads(
        subprocess.check_output(
            [
                "gh",
                "api",
                "--paginate",
                "--slurp",
                f"repos/{repository}/actions/caches?per_page=100",
            ],
            text=True,
            timeout=60,
        )
    )
    caches = [cache for page in pages for cache in page["actions_caches"]]
    obsolete = (
        obsolete_caches(caches, key)
        if key is not None
        else obsolete_main_caches(caches)
    )
    for identifier in obsolete:
        subprocess.run(
            [
                "gh",
                "api",
                "--method",
                "DELETE",
                f"repos/{repository}/actions/caches/{identifier}",
            ],
            check=True,
            timeout=60,
        )
        LOGGER.info("Removed obsolete main cache %s", identifier)


def main() -> None:
    """Print a build identity or prune main caches after replacement."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    revision = commands.add_parser("revision")
    revision.add_argument("--ref", default="HEAD")
    prune = commands.add_parser("prune")
    prune.add_argument("--repository", required=True)
    prune.add_argument(
        "--key", help="Replacement key; omit to prune all known families"
    )
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="cache: %(message)s")
    if arguments.command == "revision":
        print(build_revision(Path.cwd(), arguments.ref))
    else:
        prune_cache(arguments.repository, arguments.key)


if __name__ == "__main__":
    main()
