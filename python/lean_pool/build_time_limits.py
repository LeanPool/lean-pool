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
import select
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


def _signal_group(group: int, number: int) -> None:
    try:
        os.killpg(group, number)
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


@dataclass(frozen=True)
class OwnedProcess:
    """A Linux process identity and stable signal handle, never just a PID."""

    pid: int
    birth: int
    descriptor: int


def _process_identity(pid: int) -> tuple[int, int, int] | None:
    """Read kernel start ticks, current parent and group for a candidate PID."""
    try:
        stat = Path(f"/proc/{pid}/stat").read_text()
    except FileNotFoundError:
        return None
    fields = stat.rsplit(")", 1)[1].split()
    return int(fields[19]), int(fields[1]), int(fields[2])


def _birth(pid: int) -> int | None:
    identity = _process_identity(pid)
    return identity[0] if identity else None


def _running(process: OwnedProcess) -> bool:
    readiness = select.poll()
    readiness.register(process.descriptor, select.POLLIN)
    return not readiness.poll(0)


def _prune_owned(owned: dict[int, OwnedProcess]) -> None:
    for pid, process in list(owned.items()):
        if not _running(process):
            os.close(process.descriptor)
            del owned[pid]


def _remember(process: Process, root: int, owned: dict[int, OwnedProcess]) -> bool:
    previous = owned.get(process.pid)
    if previous is not None:
        if _running(previous):
            return True
        os.close(previous.descriptor)
        del owned[process.pid]
    try:
        descriptor = os.pidfd_open(process.pid)
    except ProcessLookupError:
        return False
    try:
        current = _process_identity(process.pid)
        if current is not None:
            birth, parent, group = current
            identity = OwnedProcess(process.pid, birth, descriptor)
            # A stale ps row may now name a recycled, unrelated PID. Prove the
            # current relationship after opening its stable handle instead.
            related = process.pid == root or group == root or parent == root
            if parent in owned and _running(owned[parent]):
                related = True
            if related and _running(identity) and _birth(process.pid) == birth:
                owned[process.pid] = identity
                return True
    except BaseException:
        os.close(descriptor)
        raise
    os.close(descriptor)
    return False


def _observe_owned(
    processes: list[Process], root: int, owned: dict[int, OwnedProcess]
) -> list[Process]:
    """Retain descendant coverage across groups, sessions and reparenting."""
    _prune_owned(owned)
    pending = {root} | {pid for pid, process in owned.items() if _running(process)}
    pending |= {process.pid for process in processes if process.group == root}
    selected, expanded = set(pending), set()
    while pending:
        expanded |= pending
        children = {process.pid for process in processes if process.parent in pending}
        pending = children - expanded
        selected |= children
    candidates = [process for process in processes if process.pid in selected]
    while candidates:
        remaining = [p for p in candidates if not _remember(p, root, owned)]
        if len(remaining) == len(candidates):
            break
        candidates = remaining
    return [
        process
        for process in processes
        if process.pid in owned
        and _running(owned[process.pid])
        and _birth(process.pid) == owned[process.pid].birth
    ]


def _signal_owned(owned: dict[int, OwnedProcess], number: int) -> None:
    for process in owned.values():
        try:
            # The pidfd pins the initially checked PID/start identity, including
            # between any last observation and the signal; PID reuse is harmless.
            signal.pidfd_send_signal(process.descriptor, number)
        except ProcessLookupError:
            pass


def _finish_group(
    root: int, owned: dict[int, OwnedProcess], poll: float, grace: float
) -> bool:
    """Finish owned cleanup and retain failures of the process observer."""
    observed = True
    try:
        # Discover children of observed intermediaries before TERM can reparent
        # them. The main loop's last process-table snapshot may already be old.
        _observe_owned(read_process_table(), root, owned)
    except (OSError, ProcessTableError, subprocess.SubprocessError, ValueError):
        observed = False
    for number in (signal.SIGTERM, signal.SIGKILL):
        _signal_group(root, number)
        _signal_owned(owned, number)
        deadline = time.monotonic() + (
            grace if number == signal.SIGTERM else max(grace, 1)
        )
        while time.monotonic() < deadline:
            try:
                _observe_owned(read_process_table(), root, owned)
            except (OSError, ProcessTableError, subprocess.SubprocessError, ValueError):
                observed = False
            if observed and not any(_running(process) for process in owned.values()):
                return True
            if number == signal.SIGKILL and not any(
                _running(process) for process in owned.values()
            ):
                return observed
            time.sleep(min(poll, 0.1, max(0, deadline - time.monotonic())))
    if any(_running(process) for process in owned.values()):
        raise RuntimeError("owned build processes survived SIGKILL")
    return observed


def _process_state(pid: int) -> str | None:
    """Read the leader state without reaping its PID or releasing its group ID."""
    try:
        stat = Path(f"/proc/{pid}/stat").read_text()
    except FileNotFoundError:
        return None
    return stat.rsplit(")", 1)[1].split()[0]


def watch(
    command: list[str],
    limit: int,
    poll: float = POLL_SECONDS,
    grace: float = TERMINATE_GRACE_SECONDS,
) -> int:
    """Run a build with identity-bound descendant monitoring and complete cleanup.

    Returns:
        124 if a Lean process exceeded its limit, 125 if observation failed,
        otherwise the command's exit status. SIGINT and SIGTERM are forwarded
        to the owned build processes while the watchdog retains cleanup duties.
    """
    if (
        not hasattr(os, "pidfd_open")
        or not hasattr(signal, "pidfd_send_signal")
        or not Path("/proc/self/stat").is_file()
    ):
        print("::error::Lean build monitoring requires Linux process identity handles")
        return 125
    child = subprocess.Popen(command, start_new_session=True)
    owned: dict[int, OwnedProcess] = {}

    def forward(number: int, _frame: object) -> None:
        _signal_group(child.pid, number)

    previous = {
        number: signal.signal(number, forward)
        for number in (signal.SIGINT, signal.SIGTERM)
    }
    status: int | None = None
    try:
        while True:
            processes = read_process_table()
            leader = next((p for p in processes if p.pid == child.pid), None)
            if leader is None or leader.group != child.pid:
                raise ProcessTableError(
                    "build process is missing from the process table"
                )
            overdue = [
                process
                for process in _observe_owned(processes, child.pid, owned)
                if is_lean_process(process) and process.elapsed > limit
            ]
            if overdue:
                for process in overdue:
                    _stop(process, limit)
                status = 124
                break
            if _process_state(child.pid) in {"Z", "X"}:
                break
            identity = owned.get(child.pid)
            if identity is not None:
                readiness = select.poll()
                readiness.register(identity.descriptor, select.POLLIN)
                readiness.poll(max(0, int(poll * 1000)))
            else:
                time.sleep(min(poll, 0.01))
    except (
        OSError,
        ProcessTableError,
        subprocess.SubprocessError,
        ValueError,
    ) as error:
        print(f"::error::Cannot monitor Lean build processes: {error}", flush=True)
        status = 125
    finally:
        # Do not reap the leader before the last signal: its unreaped PID keeps
        # the build group from being replaced by an unrelated process group.
        try:
            if not _finish_group(child.pid, owned, poll, grace):
                print(
                    "::error::Process observation failed during build cleanup",
                    flush=True,
                )
                status = 125
        finally:
            try:
                # Forwarders must be gone before the reaped PID can be reused.
                for number, handler in previous.items():
                    signal.signal(number, handler)
                returncode = child.wait()
            finally:
                for process in owned.values():
                    os.close(process.descriptor)
    return returncode if status is None else status


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


def _selected_changed_modules(
    base: str, root: Path, modules: list[str] | None
) -> dict[str, str]:
    changed = changed_modules(base, root)
    if modules is None:
        return changed
    selected = set(modules)
    return {module: path for module, path in changed.items() if module in selected}


def prepare(base: str, root: Path, modules: list[str] | None = None) -> int:
    """Invalidate changed-module artifacts so their build must record new timings."""
    changed = _selected_changed_modules(base, root, modules)
    removed = 0
    for path in changed.values():
        stem = Path(path).with_suffix("")
        for directory in ("lib/lean", "ir"):
            target = root / ".lake/build" / directory / stem
            if not target.parent.is_dir():
                continue
            for artifact in target.parent.iterdir():
                if artifact.name.startswith(target.name + ".") and (
                    artifact.is_file() or artifact.is_symlink()
                ):
                    artifact.unlink()
                    removed += 1
    print(
        f"Fresh build timings: invalidated {removed} artifacts for "
        f"{len(changed)} added or modified pool files."
    )
    return 0


def check(
    log_path: Path,
    base: str,
    root: Path,
    limit: int,
    *,
    modules: list[str] | None = None,
) -> int:
    """Report changed files over the per-file limit; return the exit status."""
    times = module_times(log_path.read_text(errors="replace"))
    changed = _selected_changed_modules(base, root, modules)
    built = [module for module in changed if module in times]
    print(
        f"Per-file build-time limit {limit} s: {len(changed)} added or modified "
        f"pool files, {len(built)} compiled in this job."
    )
    for module in sorted(built, key=lambda name: -times[name])[:10]:
        print(f"  {times[module]:8.1f} s  {changed[module]}")
    found = violations(times, changed, limit)
    missing = sorted(set(changed) - times.keys())
    for module in missing:
        print(
            f"::error file={changed[module]}::No fresh successful build timing for "
            f"{changed[module]}; added or modified files must compile in this job."
        )
    for violation in found:
        print(
            f"::error file={violation.path}::{violation.path} took "
            f"{violation.seconds:.0f} s to build; added or modified files must "
            f"build in under {limit} s on CI. Split the file or make its proofs "
            "cheaper."
        )
    return 1 if found or missing else 0


def main(arguments: list[str] | None = None) -> int:
    """Command-line entry point."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    watch_parser = commands.add_parser("watch", help="run a build under the hard limit")
    watch_parser.add_argument("--limit", type=int, default=PROCESS_LIMIT_SECONDS)
    watch_parser.add_argument("build", nargs=argparse.REMAINDER)
    prepare_parser = commands.add_parser(
        "prepare", help="force changed files to rebuild"
    )
    prepare_parser.add_argument("--base", required=True)
    prepare_parser.add_argument("--root", type=Path, default=Path.cwd())
    prepare_parser.add_argument("--modules", nargs="*")
    check_parser = commands.add_parser("check", help="check changed files' build times")
    check_parser.add_argument("--log", type=Path, required=True)
    check_parser.add_argument("--base", required=True)
    check_parser.add_argument("--limit", type=int, default=FILE_LIMIT_SECONDS)
    check_parser.add_argument("--root", type=Path, default=Path.cwd())
    check_parser.add_argument("--modules", nargs="*")
    options = parser.parse_args(arguments)
    if options.command == "watch":
        build = options.build[1:] if options.build[:1] == ["--"] else options.build
        if not build:
            parser.error("watch needs a command after --")
        return watch(build, options.limit)
    if options.command == "prepare":
        return prepare(options.base, options.root, options.modules)
    return check(
        options.log, options.base, options.root, options.limit, modules=options.modules
    )


if __name__ == "__main__":
    sys.exit(main())
