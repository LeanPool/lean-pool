"""Measure per-project build cost from Lake logs, for `plan-build-shards.py`.

Sums the `✔ [i/n] Built LeanPool.<Project>… (Ns)` lines of a cold build
into CPU seconds per pool project and prints `build-costs.json`:

    python3 scripts/ci/measure-build-costs.py --run <run id> \
        > scripts/ci/build-costs.json
    python3 scripts/ci/measure-build-costs.py shard-*.log > build-costs.json

Use a full-pool sharded run (cold cache, toolchain bump, `force_full`):
a warm run replays cached modules and under-reports their cost. Projects
absent from the logs are left out; the planner estimates them from
source size.

Only stdlib (plus the `gh` CLI for `--run`) is used, like the planner.
"""

import argparse
import json
import re
import subprocess
import sys
import time
from collections import Counter
from collections.abc import Iterable
from pathlib import Path

BUILT_LINE = re.compile(r"Built (LeanPool\.[^\s:]+) \((\d+(?:\.\d+)?)(ms|s)\)")


def project_seconds(lines: Iterable[str]) -> dict[str, int]:
    """Sum Lake's per-module build times by pool project.

    A module `LeanPool.P` or `LeanPool.P.…` belongs to project `P`, which
    covers both a project directory with its umbrella module and a
    single-file project. Facet lines such as `LeanPool.P:c.o` are skipped:
    the pool build compiles no native code.
    """
    totals: Counter[str] = Counter()
    for line in lines:
        match = BUILT_LINE.search(line)
        if match is None:
            continue
        module, value, unit = match.groups()
        seconds = float(value) / 1000 if unit == "ms" else float(value)
        totals[module.split(".")[1]] += seconds
    return {name: round(seconds) for name, seconds in sorted(totals.items())}


def gh(arguments: list[str]) -> str:
    """Run a `gh` command, retrying GitHub's transient 5xx failures."""
    for attempt in range(3):
        try:
            return subprocess.check_output(
                ["gh", *arguments], text=True, errors="replace"
            )
        except subprocess.CalledProcessError:
            if attempt == 2:
                raise
            time.sleep(10 * (attempt + 1))
    raise AssertionError("unreachable")


def shard_logs(run_id: str, repository: str) -> list[str]:
    """Download the `Build shard` job logs of a workflow run."""
    jobs = gh(
        [
            "run",
            "view",
            run_id,
            "--repo",
            repository,
            "--json",
            "jobs",
            "--jq",
            '.jobs[] | select(.name | startswith("Build shard")) | .databaseId',
        ]
    ).split()
    if not jobs:
        raise SystemExit(f"run {run_id} has no `Build shard` jobs")
    return [gh(["api", f"repos/{repository}/actions/jobs/{job}/logs"]) for job in jobs]


def main() -> None:
    """Print measured build costs as JSON."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("logs", nargs="*", type=Path, help="Lake build logs")
    parser.add_argument("--run", help="workflow run whose shard logs to fetch")
    parser.add_argument("--repository", default="LeanPool/lean-pool")
    arguments = parser.parse_args()
    if bool(arguments.logs) == bool(arguments.run):
        parser.error("pass either log files or --run")
    if arguments.run:
        texts = shard_logs(arguments.run, arguments.repository)
        source = (
            f"https://github.com/{arguments.repository}/actions/runs/{arguments.run}"
        )
    else:
        texts = [path.read_text(errors="replace") for path in arguments.logs]
        source = ", ".join(path.name for path in arguments.logs)
    seconds = project_seconds(line for text in texts for line in text.splitlines())
    if not seconds:
        raise SystemExit("no `Built LeanPool.…` lines found")
    document = {
        "description": (
            "CPU seconds per pool project in a cold CI build, summed from "
            "Lake's `Built` lines; regenerate with "
            "scripts/ci/measure-build-costs.py."
        ),
        "source": source,
        "seconds": seconds,
    }
    json.dump(document, sys.stdout, indent=1)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
