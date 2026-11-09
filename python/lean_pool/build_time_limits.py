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
import glob
import hashlib
import logging
import os
import re
import signal
import subprocess
import sys
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

LOGGER = logging.getLogger(__name__)

PROCESS_LIMIT_SECONDS = 3600
FILE_LIMIT_SECONDS = 600
POLL_SECONDS = 15
TERMINATE_GRACE_SECONDS = 30
# Written into `.lake/build` after a passing check. A restored build without the
# current policy's marker predates this gate, so changed files in it are rebuilt.
POLICY_MARKER = Path(".lake/build/lean-pool-build-time-policy")
BUILD_OUTPUT_DIRECTORIES = (Path(".lake/build/lib/lean"), Path(".lake/build/ir"))

_BUILT_LINE = re.compile(
    r"Built (?P<module>LeanPool(?:\.[^\s:()]+)+) "
    r"\((?P<value>\d+(?:\.\d+)?)(?P<unit>ms|s)\)"
)
_ELAPSED = re.compile(
    r"^(?:(?:(?P<days>\d+)-)?(?P<hours>\d+):)?(?P<minutes>\d+):(?P<seconds>\d+)$"
)


class ProcessTableError(RuntimeError):
    """``ps`` failed, so the watchdog cannot see the build's processes."""


@dataclass(frozen=True)
class Process:
    """One row of the process table."""

    pid: int
    parent: int
    group: int
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
    """Parse ``ps -A -o pid=,ppid=,pgid=,etime=,args=`` output."""
    processes = []
    for line in output.splitlines():
        fields = line.split(None, 4)
        if len(fields) < 4:
            continue
        try:
            processes.append(
                Process(
                    pid=int(fields[0]),
                    parent=int(fields[1]),
                    group=int(fields[2]),
                    elapsed=parse_elapsed(fields[3]),
                    arguments=fields[4] if len(fields) > 4 else "",
                )
            )
        except ValueError:
            continue
    return processes


def read_process_table() -> list[Process]:
    """Read the current process table portably (Linux and macOS).

    Raises:
        ProcessTableError: ``ps`` failed or printed nothing usable.
    """
    try:
        result = subprocess.run(
            ["ps", "-A", "-o", "pid=,ppid=,pgid=,etime=,args="],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        raise ProcessTableError(str(error)) from error
    processes = parse_process_table(result.stdout)
    if result.returncode != 0 or not processes:
        raise ProcessTableError(
            f"ps exited with status {result.returncode}: {result.stderr.strip()}"
        )
    return processes


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


def owned_processes(processes: list[Process], root: int) -> list[Process]:
    """Processes the build owns: its process group plus any descendants.

    The build runs as the leader of its own process group, so a Lean process
    stays owned even after its parent exits and it is reparented.
    """
    children: dict[int, list[Process]] = {}
    for process in processes:
        children.setdefault(process.parent, []).append(process)
    owned = {process.pid: process for process in processes if process.group == root}
    pending = [root, *owned]
    while pending:
        for child in children.get(pending.pop(), []):
            if child.pid not in owned:
                owned[child.pid] = child
                pending.append(child.pid)
    owned.pop(root, None)
    return list(owned.values())


def overdue_lean_processes(
    processes: list[Process], root: int, limit: int
) -> list[Process]:
    """Lean processes owned by the build that have run longer than ``limit``."""
    return [
        process
        for process in owned_processes(processes, root)
        if is_lean_process(process) and process.elapsed > limit
    ]


def _signal(pid: int, number: int) -> None:
    try:
        os.kill(pid, number)
    except ProcessLookupError:
        pass


def _signal_group(group: int, number: int) -> bool:
    """Signal a process group; ``False`` once no member is left."""
    try:
        os.killpg(group, number)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _stop(process: Process, limit: int) -> None:
    source = source_of(process)
    print(
        f"::error file={source}::{source} was still compiling after {limit // 60} "
        f"minutes and was stopped. Lean Pool's hard limit for one file is "
        f"{limit // 60} minutes; split the file or make its proofs cheaper.",
        flush=True,
    )
    _signal(process.pid, signal.SIGTERM)


def _end_group(group: int, grace: float, reap: Callable[[], object]) -> None:
    """Stop every process left in the build's group: TERM, then KILL after grace."""
    reap()
    if not _signal_group(group, signal.SIGTERM):
        return
    deadline = time.monotonic() + grace
    while time.monotonic() < deadline:
        reap()
        if not _signal_group(group, 0):
            return
        time.sleep(min(0.1, grace))
    _signal_group(group, signal.SIGKILL)


def _enforce(
    root: int,
    limit: int,
    grace: float,
    stopped: dict[tuple[int, str], float],
) -> None:
    """Stop newly overdue Lean processes and kill ones that ignored the stop."""
    processes = read_process_table()
    now = time.monotonic()
    alive = {(process.pid, process.arguments) for process in processes}
    for process in overdue_lean_processes(processes, root, limit):
        identity = (process.pid, process.arguments)
        if identity not in stopped:
            _stop(process, limit)
            stopped[identity] = now
    for identity, since in stopped.items():
        if identity in alive and now - since > grace:
            _signal(identity[0], signal.SIGKILL)


def watch(
    command: list[str],
    limit: int,
    poll: float = POLL_SECONDS,
    grace: float = TERMINATE_GRACE_SECONDS,
) -> int:
    """Run ``command``, stopping any Lean process that exceeds ``limit`` seconds.

    The command runs in its own process group. Before returning, every process
    left in that group is stopped, so nothing outlives the watchdog and keeps
    the build's output open. If ``ps`` fails, the build is stopped rather than
    left running unwatched.

    Returns:
        124 if a Lean process was stopped, 125 if the process table could not be
        read, otherwise the command's exit status.
    """
    child = subprocess.Popen(command, start_new_session=True)
    root = child.pid
    stopped: dict[tuple[int, str], float] = {}

    def forward(number: int, _frame: object) -> None:
        _signal_group(root, number)

    previous = {
        number: signal.signal(number, forward)
        for number in (signal.SIGINT, signal.SIGTERM)
    }
    status = None
    try:
        while True:
            running = child.poll() is None
            try:
                _enforce(root, limit, grace, stopped)
            except ProcessTableError as error:
                print(
                    f"::error::Cannot read the process table ({error}); "
                    "stopping the build instead of running it without the "
                    "60-minute limit.",
                    flush=True,
                )
                status = 125
                break
            if not running:
                break
            try:
                child.wait(timeout=poll)
            except subprocess.TimeoutExpired:
                pass
    finally:
        _end_group(root, grace, child.poll)
        child.wait()
        for number, handler in previous.items():
            signal.signal(number, handler)
    if status is not None:
        return status
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


def policy_digest() -> str:
    """Identify this gate's code, so a change to the limits counts as a new policy."""
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def prepare(base: str, root: Path) -> int:
    """Make Lake recompile changed files unless the restored build passed this gate.

    A build restored from a cache saved before this policy (or under different
    limits) could replay a changed file that was never timed. Deleting that file's
    outputs makes Lake compile it again, so ``check`` measures it.
    """
    marker = root / POLICY_MARKER
    if marker.is_file() and marker.read_text().strip() == policy_digest():
        print("Restored build passed the current build-time policy.")
        return 0
    removed = 0
    for module in changed_modules(base, root):
        relative = Path(*module.split("."))
        for directory in BUILD_OUTPUT_DIRECTORIES:
            folder = root / directory / relative.parent
            for output in folder.glob(glob.escape(relative.name) + ".*"):
                if output.is_file():
                    output.unlink()
                    removed += 1
    print(
        "Restored build predates the current build-time policy; removed "
        f"{removed} compiled outputs of changed files so they are rebuilt and timed."
    )
    return 0


def mark_policy(root: Path) -> None:
    """Record that every changed file in this build passed the current policy."""
    build = root / POLICY_MARKER.parent
    if build.is_dir():
        (root / POLICY_MARKER).write_text(policy_digest() + "\n")


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
    if found:
        return 1
    mark_policy(root)
    return 0


def main(arguments: list[str] | None = None) -> int:
    """Command-line entry point."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    watch_parser = commands.add_parser("watch", help="run a build under the hard limit")
    watch_parser.add_argument("--limit", type=int, default=PROCESS_LIMIT_SECONDS)
    watch_parser.add_argument("build", nargs=argparse.REMAINDER)
    prepare_parser = commands.add_parser(
        "prepare", help="rebuild changed files that a restored build never timed"
    )
    prepare_parser.add_argument("--base", required=True)
    prepare_parser.add_argument("--root", type=Path, default=Path.cwd())
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
    if options.command == "prepare":
        return prepare(options.base, options.root)
    return check(options.log, options.base, options.root, options.limit)


if __name__ == "__main__":
    sys.exit(main())
