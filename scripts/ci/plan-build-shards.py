"""Decide how the CI build is parallelized, from the change set alone.

Emits a JSON plan on stdout for the `Lean Action CI` workflow:

    {"mode": "skip" | "single" | "sharded",
     "shard_count": <int>,
     "matrix": {"include": [{"shard": "00", "projects": "ProjA ProjB"}, ...]},
     "shard_seconds": [<predicted CPU seconds per shard>, ...],
     "reason": "<human-readable explanation>"}

`skip` handles an exact README-only change. `single` keeps the
classic one-job pipeline — the fast path for a typical PR that adds or edits
one project. `sharded` splits the build across
parallel jobs for the cases that take hours serially: a cold cache, a
toolchain/manifest bump, or a refactor touching many projects.

Everything is computed at run time from the repository tree and the diff,
so there is no static shard assignment to maintain as the pool grows.
Projects are the shard unit because pool projects never import each
other. Shards are balanced by predicted build cost using greedy
longest-processing-time assignment, deterministically (ties break on
name). A project's cost is its measured CPU seconds from a cold build
(`build-costs.json`, written by `measure-build-costs.py`); a project
without a measurement is estimated from its Lean source size, scaled by
the measured projects' seconds per byte. File count is a poor proxy: a
certificate project can hold a few files that each take 15 minutes of
kernel checking. Whether to shard, and how many shards, still depends on
file count.

Environment:
    CHANGED_FILES_PATH
                    File listing the changed paths, one per line (unset or
                    empty when none).
    DIFF_AVAILABLE  "false" when no diff exists for this event
                    (workflow_dispatch, force-push); default "true".
    COLD            "true" when no warm Actions build cache matched.
    FORCE_FULL      "true" to shard-build the whole pool regardless.
"""

import json
import math
import os
import sys
from pathlib import Path

MAX_SHARDS = 10
FILES_PER_SHARD = 250
# Below either threshold a serial build is already fast; sharding would
# only add scheduling and artifact overhead to the common import PR.
SHARD_MIN_PROJECTS = 4
SHARD_MIN_FILES = 500
# Changes to any of these invalidate the whole pool's build.
GLOBAL_BUILD_INPUTS = {
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "scripts/ci/LeanPoolLinters.lean",
}
BUILD_COSTS_PATH = Path(__file__).with_name("build-costs.json")


def unit_sources() -> dict[str, list[Path]]:
    """Map each pool build unit to its Lean sources.

    A unit is a project directory (plus its umbrella module) or, for
    single-file projects like `LeanPool/CramerWold.lean`, the bare
    top-level module itself.
    """
    units: dict[str, list[Path]] = {}
    for entry in Path("LeanPool").iterdir():
        if entry.is_dir() and entry.name != "projects":
            sources = list(entry.rglob("*.lean"))
            umbrella = entry.with_suffix(".lean")
            if umbrella.exists():
                sources.append(umbrella)
            units[entry.name] = sources
        elif entry.suffix == ".lean" and not entry.with_suffix("").is_dir():
            units[entry.stem] = [entry]
    return units


def load_measured_costs(path: Path = BUILD_COSTS_PATH) -> dict[str, float]:
    """Read measured CPU seconds per project; empty if unavailable.

    A missing or malformed file only degrades balance, so it must not
    fail the build plan.
    """
    try:
        seconds = json.loads(path.read_text())["seconds"]
        return {str(name): float(value) for name, value in seconds.items()}
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        print(f"warning: ignoring build costs {path}: {error!r}", file=sys.stderr)
        return {}


def project_costs(
    source_bytes: dict[str, int], measured: dict[str, float]
) -> dict[str, float]:
    """Predict each unit's build cost in CPU seconds.

    Measured units keep their measurement. Others get their source size
    times the measured units' aggregate seconds per byte, so estimates and
    measurements share a scale.
    """
    known = [name for name in source_bytes if name in measured]
    known_bytes = sum(source_bytes[name] for name in known)
    rate = sum(measured[name] for name in known) / known_bytes if known_bytes else 1.0
    return {
        name: measured[name] if name in measured else size * rate
        for name, size in source_bytes.items()
    }


def dirty_projects(changed_files: list[str], known: set[str]) -> set[str]:
    """Projects whose directory or umbrella module appears in the diff."""
    dirty: set[str] = set()
    for path in changed_files:
        parts = path.split("/")
        if parts[0] != "LeanPool" or len(parts) < 2:
            continue
        name = parts[1].removesuffix(".lean") if len(parts) == 2 else parts[1]
        if name in known:
            dirty.add(name)
    return dirty


def assign_shards(
    targets: dict[str, float], shard_count: int
) -> list[tuple[float, list[str]]]:
    """Greedy LPT bin-packing of projects into `shard_count` balanced shards.

    Returns each non-empty shard's total cost and members.
    """
    loads = [0.0] * shard_count
    members: list[list[str]] = [[] for _ in range(shard_count)]
    for name, cost in sorted(targets.items(), key=lambda kv: (-kv[1], kv[0])):
        index = min(range(shard_count), key=lambda shard: (loads[shard], shard))
        members[index].append(name)
        loads[index] += cost
    return [(load, names) for load, names in zip(loads, members) if names]


def sharded_plan(
    sources: dict[str, list[Path]], targets: set[str], shard_count: int, reason: str
) -> dict:
    """Bin-pack `targets` into cost-balanced shards and describe the plan."""
    source_bytes = {
        name: sum(path.stat().st_size for path in paths)
        for name, paths in sources.items()
    }
    costs = project_costs(source_bytes, load_measured_costs())
    shards = assign_shards({name: costs[name] for name in targets}, shard_count)
    return {
        "mode": "sharded",
        "shard_count": len(shards),
        "matrix": {
            "include": [
                {"shard": f"{index:02d}", "projects": " ".join(sorted(members))}
                for index, (_, members) in enumerate(shards)
            ]
        },
        "shard_seconds": [round(load) for load, _ in shards],
        "reason": f"sharded ({len(shards)}): {reason}",
    }


def main() -> None:
    """Read the change set from the environment and print the build plan."""
    changed_files_path = os.environ.get("CHANGED_FILES_PATH", "")
    changed_files = (
        Path(changed_files_path).read_text().split() if changed_files_path else []
    )
    diff_available = os.environ.get("DIFF_AVAILABLE", "true") != "false"
    cold = os.environ.get("COLD", "") == "true"
    force_full = os.environ.get("FORCE_FULL", "") == "true"

    if diff_available and changed_files == ["README.md"] and not force_full:
        plan = {
            "mode": "skip",
            "shard_count": 0,
            # Keep the matrix expression valid even though its jobs are skipped.
            "matrix": {"include": [{"shard": "00", "projects": ""}]},
            "reason": "README-only change",
        }
        print(json.dumps(plan))
        return

    sources = unit_sources()
    file_counts = {name: len(paths) for name, paths in sources.items()}
    global_change = bool(GLOBAL_BUILD_INPUTS.intersection(changed_files))
    full = cold or force_full or global_change or not diff_available

    if full:
        targets = set(file_counts)
        if force_full:
            reason = "full rebuild requested"
        elif cold:
            reason = "no warm build cache"
        elif global_change:
            reason = "shared compiler or build inputs changed"
        else:
            reason = "no diff available for this event"
    else:
        targets = dirty_projects(changed_files, set(file_counts))
        files = sum(file_counts[name] for name in targets)
        reason = f"{len(targets)} dirty project(s), {files} files"

    total = sum(file_counts[name] for name in targets)
    if not full and (len(targets) < SHARD_MIN_PROJECTS or total < SHARD_MIN_FILES):
        plan = {
            "mode": "single",
            "shard_count": 1,
            # Placeholder so the matrix expression always parses; the
            # shard jobs are skipped by their `if:` in single mode.
            "matrix": {"include": [{"shard": "00", "projects": ""}]},
            "reason": f"single: {reason}",
        }
    else:
        shard_count = min(MAX_SHARDS, max(2, math.ceil(total / FILES_PER_SHARD)))
        plan = sharded_plan(sources, targets, shard_count, reason)
    print(json.dumps(plan))


if __name__ == "__main__":
    main()
