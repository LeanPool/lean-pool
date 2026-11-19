"""Enforce Lean Pool's per-file build-time and memory limits in CI.

The time limits follow Tau Ceti's CI performance gate:

* ``watch`` runs a build command and kills any Lean process it spawns that runs
  longer than the hard limit (60 minutes), so no single file can stall CI.
* ``check`` reads a Lake build log and fails when an added or modified pool file
  took longer than the per-file limit (600 seconds) to build.

Lake compiles four files at once on a 16 GB runner. Files that are each too
large exhaust it, and the runner then dies without naming a file. ``watch``
therefore also watches memory:

* a Lean process compiling a file the pull request adds is killed when it
  holds more than 3 GiB, so four new files always fit the runner together;
* when the machine is about to run out of memory, the Lean process holding the
  most is killed and the log names every file that was compiling.

Either way Lake reports the file as failed and goes on, so one run names
every file over its limit.

Existing files are only checked once a PR changes them. Times are the wall-clock
times Lake reports for each module on the CI runner.

``check`` records each changed module's time in a receipt beside its compiled
output, bound to the hash of that output. ``prepare`` forces a rebuild of every
changed module whose output carries no matching receipt, so a file compiled
without being timed can never pass; a later run that restores the same output
reuses the recorded time instead of compiling the file again. Standard library
only, so CI can run it with the runner's ``python3`` before ``uv`` is installed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
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
# Anonymous memory a Lean process may hold while it compiles a file that the
# pull request adds. Four such processes, the mapped imports they share and
# the system must fit a 16 GB runner without swapping.
ADDED_FILE_MEMORY_LIMIT_BYTES = 3 * 1024**3
# Free memory and swap below which the machine is about to fail.
MEMORY_FLOOR_BYTES = 1536 * 1024**2
# Peaks from this size on are listed after the build, so heavy files show.
MEMORY_REPORT_BYTES = 2 * 1024**3
# A compiling file can gain a hundred mebibytes a second, so memory needs a
# much shorter interval than the time limit would.
POLL_SECONDS = 1
# Exit status of ``watch`` when it stopped a process for memory.
MEMORY_STATUS = 123
# ``ps`` reports whole seconds, and the build starts just after the clock is read.
ELAPSED_ROUNDING_SECONDS = 2
TERMINATE_GRACE_SECONDS = 30
RECEIPT_VERSION = 1
RECEIPT_SUFFIX = ".timing.json"
# Every compiled output Lean loads for a module; a rebuild rewrites them all.
TIMED_OUTPUT_SUFFIXES = (".olean", ".olean.private", ".olean.server")
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


def process_memory(pid: int) -> int | None:
    """Anonymous memory a process holds, resident or swapped out, in bytes.

    Pages mapped from files are not counted: the compiled modules a Lean
    process imports are shared by every Lean process and can be reclaimed.
    ``None`` for a process that is gone or reports no memory, such as a zombie.
    """
    try:
        status = Path(f"/proc/{pid}/status").read_text()
    except (FileNotFoundError, ProcessLookupError):
        return None
    kibibytes = [
        int(value.split()[0])
        for key, _, value in (line.partition(":") for line in status.splitlines())
        if key in ("RssAnon", "VmSwap")
    ]
    return sum(kibibytes) * 1024 if kibibytes else None


def machine_memory(path: Path = Path("/proc/meminfo")) -> dict[str, int]:
    """The machine's memory figures in bytes, keyed as in ``/proc/meminfo``."""
    sizes = {}
    for line in path.read_text().splitlines():
        key, _, value = line.partition(":")
        if key in ("MemTotal", "MemAvailable", "SwapTotal", "SwapFree"):
            sizes[key] = int(value.split()[0]) * 1024
    return sizes


def free_memory() -> int | None:
    """Memory and swap the machine can still hand out, or ``None`` if unknown."""
    try:
        sizes = machine_memory()
        return sizes["MemAvailable"] + sizes["SwapFree"]
    except (OSError, KeyError, ValueError):
        return None


def _gibibytes(size: int) -> str:
    return f"{size / 2**30:.1f} GiB"


def added_files(base: str, root: Path) -> frozenset[str]:
    """Paths of the pool files added since ``base``."""
    output = subprocess.check_output(
        [
            "git",
            "-c",
            "core.quotePath=false",
            "diff",
            "--name-only",
            "--no-renames",
            "--diff-filter=A",
            f"{base}...HEAD",
            "--",
            "LeanPool",
        ],
        cwd=root,
        text=True,
    )
    return frozenset(path for path in output.splitlines() if module_of(path))


@dataclass(frozen=True)
class MemoryLimits:
    """What Lean processes may hold while the build runs."""

    added_file: int = ADDED_FILE_MEMORY_LIMIT_BYTES
    # Paths of the files the change adds, relative to ``root``.
    added: frozenset[str] = frozenset()
    root: Path = Path()
    floor: int = MEMORY_FLOOR_BYTES

    def source(self, process: Process) -> str:
        """The file a process compiles, relative to the repository if inside it."""
        source = source_of(process)
        root = os.path.abspath(self.root)
        relative = os.path.relpath(os.path.join(root, source), root)
        return source if relative.startswith("..") else relative


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
    except (FileNotFoundError, ProcessLookupError):
        # ProcessLookupError: the process was reaped between open and read.
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
    except (FileNotFoundError, ProcessLookupError):
        return None
    return stat.rsplit(")", 1)[1].split()[0]


class MemoryWatch:
    """Stops Lean processes for memory and remembers what each one held."""

    def __init__(self, limits: MemoryLimits) -> None:
        """Start with nothing stopped and nothing measured."""
        self.limits = limits
        # Identities, not handles: the watchdog closes a handle once its
        # process is gone, and the system then reuses the descriptor number.
        self.stopped: set[tuple[int, int]] = set()
        self.peaks: dict[str, int] = {}

    def _kill(self, identity: OwnedProcess) -> None:
        self.stopped.add((identity.pid, identity.birth))
        try:
            # Lake reports the file as failed and goes on with the others.
            signal.pidfd_send_signal(identity.descriptor, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def check(self, observed: list[Process], owned: dict[int, OwnedProcess]) -> None:
        """Look once at every Lean process of the build and stop what must stop."""
        holding: list[tuple[int, str, OwnedProcess]] = []
        for process in observed:
            identity = owned.get(process.pid)
            if identity is None or not is_lean_process(process):
                continue
            used = process_memory(process.pid)
            if used is None or (identity.pid, identity.birth) in self.stopped:
                continue
            source = self.limits.source(process)
            self.peaks[source] = max(self.peaks.get(source, 0), used)
            if source in self.limits.added and used > self.limits.added_file:
                print(
                    f"::error file={source}::{source} held {_gibibytes(used)} of "
                    f"memory while compiling and was stopped. Lean Pool's limit "
                    f"for a file a pull request adds is "
                    f"{_gibibytes(self.limits.added_file)}; split the file or "
                    f"make its proofs cheaper.",
                    flush=True,
                )
                self._kill(identity)
            else:
                holding.append((used, source, identity))
        self._relieve(holding, owned)

    def _dying(self, owned: dict[int, OwnedProcess]) -> bool:
        """Whether a process stopped earlier is still owned and still running."""
        return any(
            identity.birth == birth and _running(identity)
            for pid, birth in self.stopped
            if (identity := owned.get(pid)) is not None
        )

    def _relieve(
        self,
        holding: list[tuple[int, str, OwnedProcess]],
        owned: dict[int, OwnedProcess],
    ) -> None:
        """Stop the largest Lean process when the machine is nearly out of memory."""
        # A process killed a moment ago still holds its memory until it is gone.
        if self._dying(owned):
            return
        free = free_memory()
        if not holding or free is None or free >= self.limits.floor:
            return
        holding.sort(key=lambda entry: entry[0], reverse=True)
        used, source, identity = holding[0]
        compiling = ", ".join(f"{name} {_gibibytes(size)}" for size, name, _ in holding)
        print(
            f"::error file={source}::The machine had {_gibibytes(free)} of memory "
            f"left while these files were compiling: {compiling}. {source} held "
            f"the most and was stopped; split it or make its proofs cheaper.",
            flush=True,
        )
        self._kill(identity)

    def report(self, threshold: int = MEMORY_REPORT_BYTES) -> None:
        """List the files whose compiler held the most memory, largest first."""
        heavy = sorted(
            (
                (used, source)
                for source, used in self.peaks.items()
                if used >= threshold
            ),
            reverse=True,
        )
        for used, source in heavy:
            print(f"Peak memory {_gibibytes(used)}: {source}", flush=True)


def _announce(limit: int, memory: MemoryLimits) -> None:
    """Record the limits and the machine's memory at the top of the build log."""
    try:
        machine = machine_memory()
        available = (
            f" This machine has {_gibibytes(machine['MemTotal'])} of memory "
            f"and {_gibibytes(machine['SwapTotal'])} of swap."
        )
    except (OSError, KeyError, ValueError):
        available = ""
    print(
        f"Limits for one Lean process: {limit // 60} minutes, and "
        f"{_gibibytes(memory.added_file)} of memory for each of the "
        f"{len(memory.added)} files this change adds.{available}",
        flush=True,
    )


def watch(
    command: list[str],
    limit: int,
    poll: float = POLL_SECONDS,
    grace: float = TERMINATE_GRACE_SECONDS,
    memory: MemoryLimits | None = None,
) -> int:
    """Run a build with identity-bound descendant monitoring and complete cleanup.

    Returns:
        124 if a Lean process exceeded its time limit, 123 if one was stopped
        for memory, 125 if observation failed, otherwise the command's exit
        status. SIGINT and SIGTERM are forwarded to the owned build processes
        while the watchdog retains cleanup duties.
    """
    if (
        not hasattr(os, "pidfd_open")
        or not hasattr(signal, "pidfd_send_signal")
        or not Path("/proc/self/stat").is_file()
    ):
        print("::error::Lean build monitoring requires Linux process identity handles")
        return 125
    memory_watch = MemoryWatch(memory or MemoryLimits())
    _announce(limit, memory_watch.limits)
    started = time.monotonic()
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
            observed = _observe_owned(processes, child.pid, owned)
            # No process of the build is older than the build. ``ps`` can
            # report a newborn process as millions of days old; such a row
            # must not count as a file that ran over its limit.
            oldest = time.monotonic() - started + ELAPSED_ROUNDING_SECONDS
            overdue = [
                process
                for process in observed
                if is_lean_process(process) and limit < process.elapsed <= oldest
            ]
            if overdue:
                for process in overdue:
                    _stop(process, limit)
                status = 124
                break
            memory_watch.check(observed, owned)
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
    memory_watch.report()
    if status is None and memory_watch.stopped:
        return MEMORY_STATUS
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
    """Changed modules this job is responsible for timing.

    A shard names its own ``modules``. Every other job, including the one that
    assembles the shards' outputs, answers for all changed modules: whatever it
    compiles itself is timed like any other build.
    """
    changed = changed_modules(base, root)
    if modules is None:
        return changed
    selected = set(modules)
    return {module: path for module, path in changed.items() if module in selected}


def _output_stem(root: Path, path: str) -> Path:
    """``LeanPool/A/B.lean`` -> ``<root>/.lake/build/lib/lean/LeanPool/A/B``."""
    return root / ".lake/build/lib/lean" / Path(path).with_suffix("")


def output_digest(root: Path, path: str) -> str | None:
    """Hash a module's compiled outputs; ``None`` when it has not been compiled."""
    stem = _output_stem(root, path)
    digest = hashlib.sha256()
    for suffix in TIMED_OUTPUT_SUFFIXES:
        output = stem.with_name(stem.name + suffix)
        try:
            content = output.read_bytes()
        except OSError:
            if suffix == ".olean":
                return None
            continue
        digest.update(f"{suffix}:{len(content)}:".encode())
        digest.update(content)
    return digest.hexdigest()


def recorded_seconds(root: Path, path: str) -> float | None:
    """The build time recorded for the module's current outputs, if any.

    A module without compiled output has no recorded time, whatever its
    receipt says.
    """
    digest = output_digest(root, path)
    if digest is None:
        return None
    stem = _output_stem(root, path)
    try:
        receipt = json.loads(stem.with_name(stem.name + RECEIPT_SUFFIX).read_text())
        seconds = receipt["seconds"]
        valid = (
            receipt["version"] == RECEIPT_VERSION
            and isinstance(seconds, int | float)
            and not isinstance(seconds, bool)
            and seconds >= 0
            and receipt["outputs"] == digest
        )
    except (OSError, ValueError, KeyError, TypeError):
        return None
    return float(seconds) if valid else None


def record_seconds(root: Path, path: str, seconds: float) -> None:
    """Bind a freshly measured build time to the outputs that build produced."""
    digest = output_digest(root, path)
    if digest is None:
        return
    stem = _output_stem(root, path)
    receipt = {"version": RECEIPT_VERSION, "seconds": seconds, "outputs": digest}
    temporary = stem.with_name(stem.name + RECEIPT_SUFFIX + ".tmp")
    temporary.write_text(json.dumps(receipt, sort_keys=True) + "\n")
    temporary.replace(stem.with_name(stem.name + RECEIPT_SUFFIX))


def _invalidate(root: Path, path: str) -> int:
    """Remove every artifact of one module, including its timing receipt."""
    stem = Path(path).with_suffix("")
    removed = 0
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
    return removed


def prepare(base: str, root: Path, modules: list[str] | None = None) -> int:
    """Invalidate changed modules whose compiled outputs have no recorded time."""
    changed = _selected_changed_modules(base, root, modules)
    untimed = [
        path for path in changed.values() if recorded_seconds(root, path) is None
    ]
    removed = sum(_invalidate(root, path) for path in untimed)
    print(
        f"Build timings: {len(changed)} added or modified pool files, "
        f"{len(changed) - len(untimed)} with a recorded time for their compiled "
        f"output; invalidated {removed} artifacts of the other {len(untimed)}."
    )
    return 0


def changed_times(
    times: dict[str, float], changed: dict[str, str], root: Path
) -> tuple[dict[str, float], int]:
    """Each changed module's time: measured in this job, else recorded earlier.

    Returns the times and how many came from this job's build.
    """
    result = {}
    fresh = 0
    for module, path in changed.items():
        if module in times:
            record_seconds(root, path, times[module])
            result[module] = times[module]
            fresh += 1
            continue
        seconds = recorded_seconds(root, path)
        if seconds is not None:
            result[module] = seconds
    return result, fresh


def check(
    log_path: Path,
    base: str,
    root: Path,
    limit: int,
    *,
    modules: list[str] | None = None,
) -> int:
    """Report changed files over the per-file limit; return the exit status."""
    built = module_times(log_path.read_text(errors="replace"))
    changed = _selected_changed_modules(base, root, modules)
    times, fresh = changed_times(built, changed, root)
    print(
        f"Per-file build-time limit {limit} s: {len(changed)} added or modified "
        f"pool files, {fresh} compiled in this job, {len(times) - fresh} with a "
        "time recorded when their current output was compiled."
    )
    for module in sorted(times, key=lambda name: -times[name])[:10]:
        print(f"  {times[module]:8.1f} s  {changed[module]}")
    found = violations(times, changed, limit)
    missing = sorted(set(changed) - times.keys())
    for module in missing:
        print(
            f"::error file={changed[module]}::No successful build timing for "
            f"{changed[module]}; added or modified files must be compiled and "
            "timed in CI."
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
    watch_parser.add_argument(
        "--base", help="files added since this commit get the added-file memory limit"
    )
    watch_parser.add_argument("--root", type=Path, default=Path.cwd())
    watch_parser.add_argument("build", nargs=argparse.REMAINDER)
    prepare_parser = commands.add_parser(
        "prepare", help="force untimed changed files to rebuild"
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
        added = added_files(options.base, options.root) if options.base else frozenset()
        return watch(
            build, options.limit, memory=MemoryLimits(added=added, root=options.root)
        )
    if options.command == "prepare":
        return prepare(options.base, options.root, options.modules)
    return check(
        options.log, options.base, options.root, options.limit, modules=options.modules
    )


if __name__ == "__main__":
    sys.exit(main())
