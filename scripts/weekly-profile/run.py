#!/usr/bin/env python3
"""Capture, audit and publish the weekly LeanPool source profile on the VM."""

import fcntl
import json
import logging
import os
import shutil
import subprocess
from datetime import UTC, datetime
from pathlib import Path

LOGGER = logging.getLogger(__name__)
POOL_URL = "https://github.com/LeanPool/lean-pool.git"
PROFILER_URL = "https://github.com/Vilin97/lean-source-profiler.git"
GENERATED = (
    "data",
    "manifest.json",
    "coverage.json",
    "badge.json",
    "LEANPOOL-LICENSE",
    "LEANPOOL-NOTICE",
    "projects",
    "projects.yml",
)


def command(*arguments: str, directory: Path, capture: bool = False) -> str:
    """Run a command without a shell, retaining its normal diagnostic output."""
    result = subprocess.run(
        arguments,
        cwd=directory,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
    )
    return result.stdout.strip() if capture else ""


def read_json(path: Path) -> dict:
    """Read a saved run checkpoint."""
    return json.loads(path.read_text())


def write_json(path: Path, value: dict) -> None:
    """Atomically replace a checkpoint on the persistent disk."""
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def checkout_has_head(repository: Path) -> bool:
    """Check whether a private checkout has a usable committed revision."""
    try:
        command(
            "git", "rev-parse", "--verify", "HEAD", directory=repository, capture=True
        )
    except subprocess.CalledProcessError:
        return False
    return True


def preserve_incomplete_checkout(repository: Path) -> None:
    """Keep an old incomplete destination before retrying its clone."""
    if repository.is_symlink() or (repository.exists() and not repository.is_dir()):
        raise RuntimeError(
            f"The private checkout path is not a directory: {repository}"
        )
    if repository.exists() and not checkout_has_head(repository):
        preserved = repository.with_name(repository.name + ".incomplete")
        if preserved.exists() or preserved.is_symlink():
            raise RuntimeError(
                f"An incomplete checkout is already preserved: {preserved}"
            )
        repository.rename(preserved)


def clone_checkout(root: Path, name: str, url: str) -> None:
    """Promote a clean clone atomically, resetting only owned partial staging."""
    repository, temporary = root / name, root / f".{name}.clone"
    ownership = root / f".{name}.clone-owner.json"
    expected = {"repository": name, "url": url, "temporary": str(temporary)}
    if ownership.is_symlink() or temporary.is_symlink():
        raise RuntimeError("Clone staging must not use symbolic links.")
    if ownership.exists():
        if read_json(ownership) != expected:
            raise RuntimeError("Clone staging belongs to a different checkout.")
    elif temporary.exists():
        raise RuntimeError("Unowned clone staging must be preserved.")
    else:
        write_json(ownership, expected)
    if temporary.exists() and not checkout_has_head(temporary):
        shutil.rmtree(temporary)
    if not temporary.exists():
        command(
            "git",
            "clone",
            "--depth",
            "1",
            "--single-branch",
            url,
            str(temporary),
            directory=root,
        )
    command("git", "diff", "--exit-code", "HEAD", directory=temporary)
    origin = command(
        "git", "remote", "get-url", "origin", directory=temporary, capture=True
    )
    if origin != url:
        raise RuntimeError("Clone staging has a different origin.")
    if repository.exists() or repository.is_symlink():
        raise RuntimeError("The checkout destination appeared during cloning.")
    temporary.rename(repository)
    ownership.unlink()


def checkout(root: Path, name: str, url: str, revision: str = "main") -> str:
    """Prepare a private checkout and return its pinned commit."""
    repository = root / name
    preserve_incomplete_checkout(repository)
    if not repository.exists():
        clone_checkout(root, name, url)
    command("git", "diff", "--exit-code", "HEAD", directory=repository)
    command("git", "fetch", "--depth", "1", "origin", revision, directory=repository)
    command("git", "checkout", "--detach", "FETCH_HEAD", directory=repository)
    return command("git", "rev-parse", "HEAD", directory=repository, capture=True)


def run_state(root: Path) -> dict:
    """Resume an unfinished run or pin current main for a new weekly run."""
    checkpoint = root / "active.json"
    if checkpoint.exists():
        state = read_json(checkpoint)
        if state["phase"] != "complete":
            LOGGER.info("Resuming %s at %s", state["runId"], state["phase"])
            for name, key in (("repository", "commit"), ("profiler", "profilerCommit")):
                actual = command(
                    "git", "rev-parse", "HEAD", directory=root / name, capture=True
                )
                if actual != state[key]:
                    raise RuntimeError(f"The pinned {name} checkout changed.")
            return state
    commit = checkout(root, "repository", POOL_URL)
    profiler_commit = checkout(root, "profiler", PROFILER_URL)
    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    state = {
        "runId": f"{stamp}-{commit[:12]}",
        "commit": commit,
        "profilerCommit": profiler_commit,
        "phase": "prepare",
    }
    (root / "runs" / state["runId"]).mkdir(parents=True)
    write_json(checkpoint, state)
    return state


def replace_generated(export: Path, destination: Path) -> None:
    """Replace the dataset while keeping the publisher's current viewer assets."""
    for name in GENERATED:
        target, source = destination / name, export / name
        if target.is_dir():
            shutil.rmtree(target)
        elif target.exists():
            target.unlink()
        if source.is_dir():
            shutil.copytree(source, target)
        elif source.exists():
            shutil.copyfile(source, target)


def publish(run: Path, state: dict) -> str:
    """Publish with a normal Git push, retrying races without overwriting main."""
    export = run / "export"
    coverage, manifest = (
        read_json(export / "coverage.json"),
        read_json(export / "manifest.json"),
    )
    if coverage["result"] != "PASS" or manifest["commit"] != state["commit"]:
        raise RuntimeError(
            "Publication requires audited coverage for this pinned commit."
        )
    for attempt in range(1, 4):
        publisher = run / f"publish-{attempt}"
        if publisher.exists():
            shutil.rmtree(publisher)
        command(
            "git",
            "clone",
            "--depth",
            "1",
            "--single-branch",
            PROFILER_URL,
            str(publisher),
            directory=run,
        )
        previous = read_json(publisher / "docs/pool/manifest.json")
        if previous["completedAt"] >= manifest["completedAt"]:
            LOGGER.info("This recording is already published or superseded.")
            return command(
                "git", "rev-parse", "HEAD", directory=publisher, capture=True
            )
        replace_generated(export, publisher / "docs/pool")
        command("git", "add", "--", "docs/pool", directory=publisher)
        command(
            "git",
            "commit",
            "-m",
            f"Update LeanPool source profile ({state['commit'][:12]})",
            directory=publisher,
        )
        try:
            command("git", "push", "origin", "HEAD:main", directory=publisher)
        except subprocess.CalledProcessError:
            if attempt == 3:
                raise
            LOGGER.info("Retrying publication from current main.")
            continue
        return command("git", "rev-parse", "HEAD", directory=publisher, capture=True)
    raise RuntimeError("Publication did not complete.")


def prune_recordings(root: Path, keep: int = 2) -> None:
    """Retain the two most recent successful recordings and all unfinished runs."""
    completed = sorted(path.parent for path in (root / "runs").glob("*/complete.json"))
    for run in completed[:-keep]:
        LOGGER.info("Removing retained recording %s", run.name)
        shutil.rmtree(run)


def require_profile_space(root: Path, phase: str) -> None:
    """Keep the profiling disk guard while allowing saved publication recovery."""
    if phase != "publish" and shutil.disk_usage(root).free < 30 * 1024**3:
        raise RuntimeError("Profiling requires at least 30 GiB free on /data.")


def checked_run_state(root: Path) -> dict:
    """Check space before a fresh checkout or a persisted profiling stage."""
    checkpoint = root / "active.json"
    phase = read_json(checkpoint)["phase"] if checkpoint.exists() else "prepare"
    require_profile_space(root, phase)
    return run_state(root)


def execute_profile_stage(root: Path, state: dict) -> None:
    """Run one nonpublication stage after its disk-space admission."""
    phase = state["phase"]
    require_profile_space(root, phase)
    repository, profiler = root / "repository", root / "profiler"
    run = root / "runs" / state["runId"]
    if phase == "prepare":
        lake = os.environ.get("LAKE", "/data/.elan/bin/lake")
        command("npm", "ci", "--cache", str(root / "npm-cache"), directory=profiler)
        command("npm", "run", "build", directory=profiler)
        command(lake, "exe", "cache", "get", directory=repository)
    elif phase == "capture":
        command(
            "node",
            "scripts/capture-whole-pool.cjs",
            str(repository),
            str(run / "recording"),
            directory=profiler,
        )
    elif phase == "export":
        command(
            "python3",
            "scripts/export-whole-pool.py",
            str(run / "recording"),
            str(run / "export"),
            directory=profiler,
        )
    else:
        raise RuntimeError(f"Not a profiling stage: {phase}")


def execute(root: Path, state: dict) -> None:
    """Advance persisted stages; failures retry the same recording and commits."""
    run = root / "runs" / state["runId"]

    def advance(phase: str) -> None:
        state["phase"] = phase
        write_json(root / "active.json", state)
        LOGGER.info("%s: %s", state["runId"], phase)

    if state["phase"] == "prepare":
        execute_profile_stage(root, state)
        advance("capture")
    if state["phase"] == "capture":
        execute_profile_stage(root, state)
        advance("export")
    if state["phase"] == "export":
        execute_profile_stage(root, state)
        advance("publish")
    if state["phase"] == "publish":
        state["publicationCommit"] = publish(run, state)
        write_json(run / "complete.json", {**state, "phase": "complete"})
        advance("complete")
        (root / "pending").unlink(missing_ok=True)
        try:
            prune_recordings(root)
        except OSError:
            LOGGER.exception("Could not prune completed recordings.")


def main() -> None:
    """Run once under a job lock; systemd owns scheduling and failure retries."""
    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s"
    )
    root = Path(
        os.environ.get("LEAN_POOL_PROFILE_ROOT", "/data/lean-pool-profile")
    ).resolve()
    if not root.is_relative_to(Path("/data")):
        raise RuntimeError("All profiling storage must live under /data.")
    root.mkdir(parents=True, exist_ok=True)
    with (root / "job.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            LOGGER.info("A whole-pool profiling run is already active.")
            return
        temporary = root / "tmp"
        temporary.mkdir(exist_ok=True)
        os.environ["TMPDIR"] = str(temporary)
        (root / "pending").touch()
        execute(root, checked_run_state(root))


if __name__ == "__main__":
    main()
