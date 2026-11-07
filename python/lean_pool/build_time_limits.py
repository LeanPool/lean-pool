"""Enforce Lean Pool's per-file build-time limits in CI.

Two limits apply, following Tau Ceti's CI performance gate:

* ``watch`` runs a build command and kills any Lean process it spawns that runs
  longer than the hard limit (60 minutes), so no single file can stall CI.
* ``check`` reads a Lake build log and fails when an added or modified pool file
  took longer than the per-file limit (600 seconds) to build.

Existing files are only checked once a PR changes them. Times are the wall-clock
times Lake reports for each module on the CI runner. Standard library only, so CI
can run it with the runner's ``python3`` before ``uv`` is installed.
"""

from __future__ import annotations

import argparse
import logging
import os
import re
import signal
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

LOGGER = logging.getLogger(__name__)

PROCESS_LIMIT_SECONDS = 3600
FILE_LIMIT_SECONDS = 600
POLL_SECONDS = 15
TERMINATE_GRACE_SECONDS = 30

_BUILT_LINE = re.compile(
    r"Built (?P<module>LeanPool(?:\.[^\s:()]+)+) "
    r"\((?P<value>\d+(?:\.\d+)?)(?P<unit>ms|s)\)"
)
_ELAPSED = re.compile(
    r"^(?:(?:(?P<days>\d+)-)?(?P<hours>\d+):)?(?P<minutes>\d+):(?P<seconds>\d+)$"
)


@dataclass(frozen=True)
class Process:
    """One row of the process table."""

    pid: int
    parent: int
    elapsed: int
    arguments: str


def parse_elapsed(text: str) -> int:
    """Convert ``ps`` elapsed time (``[[dd-]hh:]mm:ss``) to seconds."""
    match = _ELAPSED.match(text.strip())
    if match is None:
        raise ValueError(f"unrecognized elapsed time: {text!r}")
    parts = {key: int(value or 0) for key, value in match.groupdict().items()}
    return (
        parts["days"] * 86400
        + parts["hours"] * 3600
        + parts["minutes"] * 60
        + parts["seconds"]
    )


def parse_process_table(output: str) -> list[Process]:
    """Parse ``ps -A -o pid=,ppid=,etime=,args=`` output."""
    processes = []
    for line in output.splitlines():
        fields = line.split(None, 3)
        if len(fields) < 3:
            continue
        try:
            processes.append(
                Process(
                    pid=int(fields[0]),
                    parent=int(fields[1]),
                    elapsed=parse_elapsed(fields[2]),
                    arguments=fields[3] if len(fields) > 3 else "",
                )
            )
        except ValueError:
            continue
    return processes


def read_process_table() -> list[Process]:
    """Read the current process table portably (Linux and macOS)."""
    output = subprocess.run(
        ["ps", "-A", "-o", "pid=,ppid=,etime=,args="],
        capture_output=True,
        text=True,
        check=False,
    ).stdout
    return parse_process_table(output)


def is_lean_process(process: Process) -> bool:
    """Whether a process is a Lean compiler run (not Lake or a shell)."""
    if not process.arguments:
        return False
    return Path(process.arguments.split()[0]).name == "lean"


def source_of(process: Process) -> str:
    """The ``.lean`` file a Lean process is compiling, or its command line."""
    for argument in process.arguments.split():
        if argument.endswith(".lean"):
            return argument
    return process.arguments


def overdue_lean_processes(
    processes: list[Process], root: int, limit: int
) -> list[Process]:
    """Lean processes descended from ``root`` that have run longer than ``limit``."""
    children: dict[int, list[Process]] = {}
    for process in processes:
        children.setdefault(process.parent, []).append(process)
    overdue = []
    pending = [root]
    seen = {root}
    while pending:
        for child in children.get(pending.pop(), []):
            if child.pid in seen:
                continue
            seen.add(child.pid)
            pending.append(child.pid)
            if is_lean_process(child) and child.elapsed > limit:
                overdue.append(child)
    return overdue


def _signal(pid: int, number: int) -> None:
    try:
        os.kill(pid, number)
    except ProcessLookupError:
        pass


def _stop(process: Process, limit: int) -> None:
    source = source_of(process)
    print(
        f"::error file={source}::{source} was still compiling after {limit // 60} "
        f"minutes and was stopped. Lean Pool's hard limit for one file is "
        f"{limit // 60} minutes; split the file or make its proofs cheaper.",
        flush=True,
    )
    _signal(process.pid, signal.SIGTERM)


def watch(command: list[str], limit: int, poll: float = POLL_SECONDS) -> int:
    """Run ``command``, stopping any Lean process that exceeds ``limit`` seconds."""
    child = subprocess.Popen(command)
    stopped: dict[int, float] = {}
    while child.poll() is None:
        now = time.monotonic()
        for process in overdue_lean_processes(read_process_table(), child.pid, limit):
            if process.pid not in stopped:
                _stop(process, limit)
                stopped[process.pid] = now
            elif now - stopped[process.pid] > TERMINATE_GRACE_SECONDS:
                _signal(process.pid, signal.SIGKILL)
        try:
            child.wait(timeout=poll)
        except subprocess.TimeoutExpired:
            pass
    if stopped:
        return 124
    return child.returncode


def module_times(log: str) -> dict[str, float]:
    """Build seconds per pool module from Lake's ``Built <module> (<time>)`` lines."""
    times: dict[str, float] = {}
    for match in _BUILT_LINE.finditer(log):
        seconds = float(match["value"])
        if match["unit"] == "ms":
            seconds /= 1000
        module = match["module"]
        times[module] = max(seconds, times.get(module, 0.0))
    return times


def module_of(path: str) -> str | None:
    """``LeanPool/A/B.lean`` -> ``LeanPool.A.B``; ``None`` for other files."""
    if not (path.startswith("LeanPool/") and path.endswith(".lean")):
        return None
    return path.removesuffix(".lean").replace("/", ".")


def changed_modules(base: str, root: Path) -> dict[str, str]:
    """Pool modules added or modified since ``base``, mapped to their paths."""
    output = subprocess.check_output(
        [
            "git",
            "-c",
            "core.quotePath=false",
            "diff",
            "--name-only",
            "--no-renames",
            "--diff-filter=AM",
            f"{base}...HEAD",
            "--",
            "LeanPool",
        ],
        cwd=root,
        text=True,
    )
    modules = {}
    for path in output.splitlines():
        module = module_of(path)
        if module is not None:
            modules[module] = path
    return modules


@dataclass(frozen=True)
class Violation:
    """A changed file that took too long to build."""

    path: str
    seconds: float


def violations(
    times: dict[str, float], changed: dict[str, str], limit: int
) -> list[Violation]:
    """Changed modules whose build time exceeds ``limit``, slowest first."""
    found = [
        Violation(path=changed[module], seconds=times[module])
        for module in changed
        if times.get(module, 0.0) > limit
    ]
    return sorted(found, key=lambda violation: -violation.seconds)


def check(log_path: Path, base: str, root: Path, limit: int) -> int:
    """Report changed files over the per-file limit; return the exit status."""
    times = module_times(log_path.read_text(errors="replace"))
    changed = changed_modules(base, root)
    built = [module for module in changed if module in times]
    print(
        f"Per-file build-time limit {limit} s: {len(changed)} added or modified "
        f"pool files, {len(built)} compiled in this job."
    )
    for module in sorted(built, key=lambda name: -times[name])[:10]:
        print(f"  {times[module]:8.1f} s  {changed[module]}")
    found = violations(times, changed, limit)
    for violation in found:
        print(
            f"::error file={violation.path}::{violation.path} took "
            f"{violation.seconds:.0f} s to build; added or modified files must "
            f"build in under {limit} s on CI. Split the file or make its proofs "
            "cheaper."
        )
    return 1 if found else 0


def main(arguments: list[str] | None = None) -> int:
    """Command-line entry point."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    watch_parser = commands.add_parser("watch", help="run a build under the hard limit")
    watch_parser.add_argument("--limit", type=int, default=PROCESS_LIMIT_SECONDS)
    watch_parser.add_argument("build", nargs=argparse.REMAINDER)
    check_parser = commands.add_parser("check", help="check changed files' build times")
    check_parser.add_argument("--log", type=Path, required=True)
    check_parser.add_argument("--base", required=True)
    check_parser.add_argument("--limit", type=int, default=FILE_LIMIT_SECONDS)
    check_parser.add_argument("--root", type=Path, default=Path.cwd())
    options = parser.parse_args(arguments)
    if options.command == "watch":
        build = options.build[1:] if options.build[:1] == ["--"] else options.build
        if not build:
            parser.error("watch needs a command after --")
        return watch(build, options.limit)
    return check(options.log, options.base, options.root, options.limit)


if __name__ == "__main__":
    sys.exit(main())
