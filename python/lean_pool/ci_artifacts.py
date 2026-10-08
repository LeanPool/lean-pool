"""Share main's full build and PR project overlays with independent consumers.

Only the matching Lean Action CI run is queried. A source-tree/configuration
manifest is verified before any artifact is installed; Lake still checks its
normal build traces afterwards. Missing or incompatible artifacts fall back to
the ordinary Lake build. PR overlays preserve the shared main cache and contain
only projects changed in the author's diff, including a manifest-only archive
for infrastructure changes.
"""

from __future__ import annotations

import argparse
import filecmp
import gzip
import hashlib
import io
import json
import logging
import os
import re
import shutil
import stat
import subprocess
import tarfile
import tempfile
import time
import zipfile
from concurrent.futures import ThreadPoolExecutor
from contextlib import AbstractContextManager, contextmanager
from pathlib import Path, PurePosixPath
from typing import BinaryIO
from urllib.parse import urlencode

LOGGER = logging.getLogger(__name__)
ARTIFACT_NAME = "lean-pool-build"
ARCHIVE_NAME = "lean-pool-build.tar.zst"
LEGACY_ARCHIVE_NAME = "lean-pool-build.tar.gz"
MANIFEST_NAME = "build-manifest.json"
PROJECT = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")


def _project_output(path: PurePosixPath, projects: list[str]) -> bool:
    """Restrict overlays to the changed projects' Lean library and IR files."""
    for prefix in (
        (".lake", "build", "ir", "LeanPool"),
        (".lake", "build", "lib", "lean", "LeanPool"),
    ):
        if path.parts[: len(prefix)] == prefix and len(path.parts) > len(prefix):
            module = path.parts[len(prefix)]
            return any(
                module == name or module.startswith(name + ".") for name in projects
            )
    return False


def _changed_projects(root: Path, base: str, head: str) -> list[str]:
    """Select PR-owned projects from the author diff, excluding changes on main."""
    paths = (
        subprocess.check_output(
            ["git", "diff", "--name-only", "-z", f"{base}...{head}", "--", "LeanPool"],
            cwd=root,
        )
        .decode()
        .split("\0")
    )
    projects = sorted(
        {
            path.split("/")[1].removesuffix(".lean")
            for path in paths
            if path.startswith("LeanPool/") and path.endswith(".lean")
        }
    )
    if not all(PROJECT.fullmatch(name) for name in projects):
        raise ValueError("invalid changed project")
    return projects


def _file_digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def build_identity(root: Path) -> dict:
    """Identify the checkout tree and pinned build inputs, including merge checkouts."""
    tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD^{tree}"], cwd=root, text=True
    ).strip()
    return {
        "version": 1,
        "tree": tree,
        "inputs": {
            name: _file_digest(root / name)
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
        },
    }


@contextmanager
def _compressed_stream(path: Path, *, writing: bool = False):
    """Stream compression and verify completion before accepting an archive."""
    if path.suffix == ".gz":
        with gzip.open(path, "wb" if writing else "rb", compresslevel=1) as stream:
            yield stream
            if not writing:
                while stream.read(1024 * 1024):
                    pass
        return
    command = (
        ["zstd", "--quiet", "-1", "-T2"]
        if writing
        else ["zstd", "--quiet", "--decompress", "--stdout", str(path)]
    )
    with path.open("wb") if writing else open(os.devnull, "wb") as output:
        process = subprocess.Popen(
            command,
            stdin=subprocess.PIPE if writing else subprocess.DEVNULL,
            stdout=output if writing else subprocess.PIPE,
        )
        stream = process.stdin if writing else process.stdout
        try:
            yield stream
            if not writing:
                while stream.read(1024 * 1024):
                    pass
            stream.close()
            if process.wait() != 0:
                raise subprocess.CalledProcessError(process.returncode, command)
        finally:
            stream.close()
            if process.poll() is None:
                process.terminate()
            process.wait()


def pack_build(
    root: Path, destination: Path, *, base: str = "", head: str = ""
) -> None:
    """Package main's full build or only PR-owned projects for a verifier overlay."""
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=root, check=True)
    identity = build_identity(root)
    if bool(base) != bool(head):
        raise ValueError("project packaging requires both base and head")
    if base:
        identity["projects"] = _changed_projects(root, base, head)
    payload = json.dumps(identity).encode()
    manifest = tarfile.TarInfo(MANIFEST_NAME)
    manifest.size = len(payload)
    with _compressed_stream(destination, writing=True) as stream:
        with tarfile.open(fileobj=stream, mode="w|", dereference=True) as archive:
            archive.addfile(manifest, io.BytesIO(payload))
            if "projects" not in identity:
                archive.add(root / ".lake/build", arcname=".lake/build")
            else:
                for path in sorted((root / ".lake/build").rglob("*")):
                    relative = PurePosixPath(path.relative_to(root).as_posix())
                    if path.is_file() and _project_output(
                        relative, identity["projects"]
                    ):
                        archive.add(path, arcname=str(relative), recursive=False)


def _reuse_unchanged_file(
    root: Path,
    temporary: Path,
    member: tarfile.TarInfo,
    reused: dict[Path, os.stat_result],
) -> None:
    """Keep identical cached files without retaining a second full build copy."""
    relative = Path(member.name)
    cached = root / relative
    staged = temporary / relative
    if (
        cached.is_symlink()
        or not cached.is_file()
        or not filecmp.cmp(cached, staged, shallow=False)
    ):
        return
    reused[relative] = staged.stat()
    staged.unlink()
    staged.hardlink_to(cached)


def _extract_build(
    root: Path,
    archive: tarfile.TarFile,
    temporary: Path,
    reused: dict[Path, os.stat_result],
) -> str | None:
    """Check the manifest first, then extract only ordinary build files."""
    manifest = archive.next()
    if manifest is None or manifest.name != MANIFEST_NAME or not manifest.isfile():
        raise ValueError("Missing build archive manifest")
    identity = json.load(archive.extractfile(manifest))
    if not isinstance(identity, dict):
        raise ValueError("invalid build archive manifest")
    project_overlay = "projects" in identity
    projects = identity.pop("projects", None)
    if project_overlay and (
        not isinstance(projects, list)
        or not all(
            isinstance(name, str) and PROJECT.fullmatch(name) for name in projects
        )
    ):
        raise ValueError("invalid project overlay")
    if identity != build_identity(root):
        LOGGER.info("CI build has different sources or configuration; rebuilding")
        return None
    has_files = False
    seen: set[PurePosixPath] = set()
    for member in archive:
        if member is manifest:
            continue
        path = PurePosixPath(member.name)
        if (
            path.parts[:2] != (".lake", "build")
            or ".." in path.parts
            or path in seen
            or not (member.isfile() or member.isdir())
            or (
                projects is not None
                and (not member.isfile() or not _project_output(path, projects))
            )
        ):
            raise ValueError(f"Unexpected build archive member: {member.name}")
        seen.add(path)
        has_files |= member.isfile()
        archive.extract(member, temporary, filter="data")
        if member.isfile():
            _reuse_unchanged_file(root, temporary, member, reused)
    if not has_files and projects is None:
        raise ValueError("Empty Lean build artifact")
    return "full" if projects is None else "projects"


def restore_build(root: Path, archive_path: Path) -> bool:
    """Validate and unpack once, sharing unchanged files with the cached build."""
    return _restore_archive(root, _compressed_stream(archive_path))


def _restore_archive(root: Path, payload: AbstractContextManager[BinaryIO]) -> bool:
    """Install staged output only after the entire compressed payload validates."""
    (root / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="lean-ci-build-", dir=root / ".lake"
    ) as name:
        temporary = Path(name)
        reused: dict[Path, os.stat_result] = {}
        with payload as stream:
            with tarfile.open(fileobj=stream, mode="r|") as archive:
                mode = _extract_build(root, archive, temporary, reused)
                if not mode:
                    return False
        destination = root / ".lake/build"
        if mode == "full":
            if destination.exists():
                shutil.rmtree(destination)
            (temporary / ".lake/build").rename(destination)
        else:
            for staged in (temporary / ".lake/build").rglob("*"):
                if staged.is_file():
                    target = root / staged.relative_to(temporary)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    os.replace(staged, target)
        for relative, metadata in reused.items():
            path = root / relative
            path.chmod(stat.S_IMODE(metadata.st_mode))
            os.utime(path, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
    LOGGER.info("Restored Lean CI build for the current source tree")
    return True


def github_json(endpoint: str) -> dict:
    """Read GitHub metadata through the runner's authenticated CLI."""
    return json.loads(subprocess.check_output(["gh", "api", endpoint], timeout=60))


def matching_run(repository: str, head: str, event: str) -> dict | None:
    """Select the latest Lean CI attempt for this event and exact head revision."""
    query = urlencode({"head_sha": head, "event": event, "per_page": 10})
    endpoint = f"repos/{repository}/actions/workflows/lean_action_ci.yml/runs?{query}"
    runs = github_json(endpoint)["workflow_runs"]
    return max(runs, key=lambda run: run["id"]) if runs else None


def wait_for_artifact(repository: str, run: dict, wait_seconds: int) -> int | None:
    """Wait for compiled output without waiting for later lint/quality stages."""
    deadline = time.monotonic() + wait_seconds
    endpoint = f"repos/{repository}/actions/runs/{run['id']}"
    while True:
        artifacts = github_json(f"{endpoint}/artifacts?per_page=100")["artifacts"]
        matches = [
            artifact
            for artifact in artifacts
            if artifact["name"] == ARTIFACT_NAME and not artifact["expired"]
        ]
        if matches:
            return max(matches, key=lambda artifact: artifact["id"])["id"]
        status = github_json(endpoint)
        if status["status"] == "completed" or time.monotonic() >= deadline:
            return None
        time.sleep(min(20, max(0, deadline - time.monotonic())))


def wait_for_build(repository: str, head: str, event: str, wait: int) -> int | None:
    """Allow the producer workflow to appear, within one bounded waiting window."""
    deadline = time.monotonic() + wait
    while True:
        run = matching_run(repository, head, event)
        remaining = max(0, deadline - time.monotonic())
        if run is not None:
            return wait_for_artifact(repository, run, int(remaining))
        if remaining == 0:
            return None
        time.sleep(min(20, remaining))


def _pipe_payload(source: BinaryIO, destination: BinaryIO) -> None:
    """Feed the ZIP entry into the decompressor without materializing another file."""
    with destination:
        shutil.copyfileobj(source, destination)


@contextmanager
def _artifact_payload(source: BinaryIO, name: str):
    """Stream the compressed ZIP entry and verify decompression and ZIP integrity."""
    if name.endswith(".gz"):
        with gzip.GzipFile(fileobj=source) as stream:
            yield stream
            while stream.read(1024 * 1024):
                pass
        return
    command = ["zstd", "--quiet", "--decompress", "--stdout"]
    with subprocess.Popen(
        command, stdin=subprocess.PIPE, stdout=subprocess.PIPE
    ) as process:
        with ThreadPoolExecutor(max_workers=1) as executor:
            copying = executor.submit(_pipe_payload, source, process.stdin)
            try:
                yield process.stdout
                while process.stdout.read(1024 * 1024):
                    pass
                copying.result()
                if process.wait() != 0:
                    raise subprocess.CalledProcessError(process.returncode, command)
            finally:
                process.stdout.close()
                if process.poll() is None:
                    process.terminate()
                process.wait()


def download_build(root: Path, repository: str, artifact: int) -> bool:
    """Download the archive and validate it before installing any build files."""
    (root / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="lean-ci-download-", dir=root / ".lake"
    ) as temporary:
        directory = Path(temporary)
        zipped = directory / "artifact.zip"
        with zipped.open("wb") as output:
            subprocess.run(
                ["gh", "api", f"repos/{repository}/actions/artifacts/{artifact}/zip"],
                stdout=output,
                check=True,
                timeout=600,
            )
        with zipfile.ZipFile(zipped) as archive:
            names = archive.namelist()
            if names not in ([ARCHIVE_NAME], [LEGACY_ARCHIVE_NAME]):
                raise ValueError("Unexpected files in Lean CI artifact")
            name = names[0]
            with archive.open(name) as source:
                return _restore_archive(root, _artifact_payload(source, name))


def reuse_build(
    root: Path,
    repository: str,
    head: str,
    event: str,
    wait: int,
    *,
    pull_request_artifact: bool = False,
) -> bool:
    """Best-effort reuse; unavailable CI never removes the regular Lake build step."""
    # Only PRs requiring full minimal-file verification publish this archive.
    if event == "pull_request" and not pull_request_artifact:
        LOGGER.info(
            "PRs do not publish full build artifacts; using the regular Lake build"
        )
        return False
    try:
        run = matching_run(repository, head, event)
        if run is None:
            LOGGER.info("No matching Lean CI run; using the regular Lake build")
            return False
        LOGGER.info("Looking for compiled output from %s", run["html_url"])
        artifact = wait_for_artifact(repository, run, wait)
        if artifact is None:
            LOGGER.info(
                "No completed build artifact available; using the regular Lake build"
            )
            return False
        return download_build(root, repository, artifact)
    except (
        subprocess.SubprocessError,
        OSError,
        ValueError,
        KeyError,
        tarfile.TarError,
        EOFError,
        zipfile.BadZipFile,
    ):
        LOGGER.exception("Could not reuse CI output; using the regular Lake build")
        return False


def main() -> None:
    """Package a successful build or restore the matching workflow's compiled output."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    pack = commands.add_parser("pack")
    pack.add_argument("--output", type=Path, default=Path(ARCHIVE_NAME))
    pack.add_argument("--base", default="")
    pack.add_argument("--head", default="")
    restore = commands.add_parser("restore")
    waiting = commands.add_parser("wait")
    for command in (restore, waiting):
        command.add_argument(
            "--repository", default=os.environ.get("GITHUB_REPOSITORY")
        )
        command.add_argument("--head", required=True)
        command.add_argument("--event", required=True)
        command.add_argument("--wait-seconds", type=int, default=7200)
    restore.add_argument("--pull-request-artifact", action="store_true")
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="ci-artifacts: %(message)s")
    if arguments.command == "pack":
        pack_build(
            Path.cwd(), arguments.output, base=arguments.base, head=arguments.head
        )
    elif arguments.command == "wait":
        wait_for_build(
            arguments.repository,
            arguments.head,
            arguments.event,
            arguments.wait_seconds,
        )
    else:
        reuse_build(
            Path.cwd(),
            arguments.repository,
            arguments.head,
            arguments.event,
            arguments.wait_seconds,
            pull_request_artifact=arguments.pull_request_artifact,
        )


if __name__ == "__main__":
    main()
