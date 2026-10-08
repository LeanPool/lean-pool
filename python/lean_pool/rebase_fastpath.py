"""Reuse a green PR build after an automatic, content-only merge of main.

The fast path is deliberately narrow. It requires a successful earlier run on
the first parent of the rebase merge, unchanged PR-owned project sources, and
only LeanPool content added by main. Everything else uses ordinary CI.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile
from pathlib import Path, PurePosixPath
from typing import Any
from urllib.parse import urlencode

from lean_pool.indexes import requires_project_roots, structure_errors

ARTIFACT = "rebase-project-build"
ARCHIVE = f"{ARTIFACT}.tar.gz"
MANIFEST = "rebase-build-manifest.json"
REGISTRY = "LeanPool/projects.yml"
INDEX = "LeanPool.lean"
PINNED_INPUTS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
SHA = re.compile(r"[0-9a-f]{40}\Z")
PROJECT = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")
CARD = re.compile(r"^  - slug: ([A-Za-z0-9_-]+)[ \t]*$", re.MULTILINE)


def git(root: Path, *arguments: str) -> str:
    """Run a Git read in the checkout."""
    return subprocess.check_output(["git", *arguments], cwd=root, text=True).strip()


def paths(root: Path, before: str, after: str, *, merge_base: bool = False) -> set[str]:
    """List changed paths using NUL delimiters and no rename inference."""
    separator = "..." if merge_base else ".."
    output = subprocess.check_output(
        [
            "git",
            "diff",
            "--name-only",
            "-z",
            "--no-renames",
            f"{before}{separator}{after}",
        ],
        cwd=root,
    )
    return {os.fsdecode(path) for path in output.split(b"\0") if path}


def github_json(endpoint: str) -> Any:
    """Read repository metadata through the runner's authenticated GitHub CLI."""
    return json.loads(
        subprocess.check_output(["gh", "api", endpoint], text=True, timeout=60)
    )


def _content_path(path: str) -> bool:
    return path in {INDEX, REGISTRY} or (
        path.startswith("LeanPool/") and path.endswith(".lean")
    )


def _main_path(path: str) -> bool:
    """Allow generated metadata alongside independently verified pool content."""
    return _content_path(path) or path in {"README.md", "NOTICE"}


def _exists_at(root: Path, revision: str, path: str) -> bool:
    """Check whether a file already existed before main advanced."""
    return (
        subprocess.run(
            ["git", "cat-file", "-e", f"{revision}:{path}"],
            cwd=root,
            capture_output=True,
            check=False,
        ).returncode
        == 0
    )


def _registry_cards(root: Path, revision: str) -> dict[str, str]:
    """Split the repository's slug-first registry, rejecting unfamiliar layouts."""
    source = git(root, "show", f"{revision}:{REGISTRY}")
    if not source.startswith("projects:\n"):
        raise ValueError("unrecognized project registry layout")
    matches = list(CARD.finditer(source))
    if not matches or source[: matches[0].start()] != "projects:\n":
        raise ValueError("unrecognized project registry cards")
    cards = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        slug = match.group(1)
        if slug in cards:
            raise ValueError("duplicate project card")
        cards[slug] = source[match.start() : end].rstrip("\n")
    return cards


def _registry_rebased(
    root: Path, old_base: str, previous: str, base: str, head: str
) -> bool:
    """Require current cards to equal the new main plus unchanged PR additions."""
    before = _registry_cards(root, old_base)
    old_pr = _registry_cards(root, previous)
    main = _registry_cards(root, base)
    current = _registry_cards(root, head)
    if any(old_pr.get(slug) != card for slug, card in before.items()):
        return False
    added = {slug: card for slug, card in old_pr.items() if slug not in before}
    if set(added) & set(main):
        return False
    return current == (main | added)


def _previous_head(root: Path, head: str, base: str) -> str | None:
    """Accept the bot's merge, optionally followed by one index-only commit."""
    current = head
    for _ in range(2):
        parents = git(root, "rev-list", "--parents", "-n", "1", current).split()
        if len(parents) == 3:
            return parents[1] if parents[2] == base else None
        if len(parents) != 2 or paths(root, parents[1], current) != {INDEX}:
            return None
        current = parents[1]
    return None


def _successful_run(
    repository: str,
    workflow: str,
    number: int,
    head: str,
    *,
    merged: bool = False,
) -> dict | None:
    query = urlencode({"event": "pull_request", "head_sha": head, "per_page": 100})
    endpoint = f"repos/{repository}/actions/workflows/{workflow}/runs?{query}"
    runs = github_json(endpoint)["workflow_runs"]
    matches = [
        run
        for run in runs
        if run.get("head_sha") == head
        # GitHub clears pull_requests on workflow runs after that PR merges.
        # The caller verifies the commit-to-PR association for merged runs.
        and (
            merged
            or any(
                pull.get("number") == number for pull in run.get("pull_requests", [])
            )
        )
    ]
    if not matches:
        return None
    latest = max(matches, key=lambda run: run["id"])
    return latest if latest.get("conclusion") == "success" else None


def _has_build_artifact(repository: str, run_id: int) -> bool:
    endpoint = f"repos/{repository}/actions/runs/{run_id}/artifacts?per_page=100"
    return any(
        artifact["name"] == ARTIFACT and not artifact["expired"]
        for artifact in github_json(endpoint)["artifacts"]
    )


def decision(
    root: Path, repository: str, workflow: str, number: int, head: str, base: str
) -> dict:
    """Return a verified reuse decision; uncertainty always selects full CI."""
    result = {"eligible": False, "reason": "not a verified content-only rebase"}
    if workflow not in {"lean_action_ci.yml", "docs.yml"} or not all(
        SHA.fullmatch(value) for value in (head, base)
    ):
        return result
    previous = _previous_head(root, head, base)
    if previous is None:
        return result
    run = _successful_run(repository, workflow, number, previous)
    if run is None:
        return {**result, "reason": "no successful earlier PR run"}
    # The Actions API's embedded pull_request.base.sha follows the *current*
    # PR base, even for an older run. Git ancestry is the stable source here.
    old_base = git(root, "merge-base", previous, base)
    if not SHA.fullmatch(old_base):
        return result
    if subprocess.run(
        ["git", "merge-base", "--is-ancestor", old_base, base], cwd=root, check=False
    ).returncode:
        return result
    main_delta = paths(root, old_base, base)
    if not main_delta or not all(map(_main_path, main_delta)):
        return {**result, "reason": "main changed shared build or validation inputs"}
    if any(
        path != INDEX and path.endswith(".lean") and _exists_at(root, old_base, path)
        for path in main_delta
    ):
        return {**result, "reason": "main edited existing Lean sources"}
    old_pr = paths(root, old_base, previous, merge_base=True)
    new_pr = paths(root, base, head, merge_base=True)
    if not all(map(_content_path, old_pr | new_pr)):
        return result
    old_owned = old_pr - {INDEX, REGISTRY}
    new_owned = new_pr - {INDEX, REGISTRY}
    if old_owned != new_owned or old_owned & main_delta:
        return {**result, "reason": "PR-owned Lean sources changed"}
    for path in old_owned:
        if git(root, "rev-parse", f"{previous}:{path}") != git(
            root, "rev-parse", f"{head}:{path}"
        ):
            return {**result, "reason": "PR-owned Lean sources changed"}
    if not _registry_rebased(root, old_base, previous, base, head):
        return {**result, "reason": "project cards changed beyond the merge"}
    if workflow == "lean_action_ci.yml" and not _has_build_artifact(
        repository, run["id"]
    ):
        return {**result, "reason": "prior PR build artifact unavailable"}
    return {
        "eligible": True,
        "reason": "verified rebase",
        "run_id": run["id"],
        "previous_head": previous,
    }


def check_index(root: Path) -> bool:
    """Check the generated root without starting Lean or downloading Mathlib."""
    if requires_project_roots(root):
        return not structure_errors(root)
    pool = root / "LeanPool"
    modules = sorted(
        "LeanPool."
        + path.relative_to(pool).with_suffix("").as_posix().replace("/", ".")
        for path in pool.rglob("*.lean")
    )
    expected = "module  -- shake: keep-all --deprecated_module: ignore\n\n"
    expected += "".join(f"public import {module}\n" for module in modules)
    return (root / INDEX).read_text(encoding="utf-8") == expected


def _projects(root: Path, base: str, head: str) -> list[str]:
    return sorted(
        {
            path.split("/")[1].removesuffix(".lean")
            for path in paths(root, base, head, merge_base=True)
            if path.startswith("LeanPool/") and path.endswith(".lean")
        }
    )


def _source_hashes(root: Path, projects: list[str]) -> dict[str, str]:
    result = {}
    for project in projects:
        for path in sorted((root / "LeanPool").glob(f"{project}.lean")):
            result[path.relative_to(root).as_posix()] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
        for path in sorted((root / "LeanPool" / project).rglob("*.lean")):
            result[path.relative_to(root).as_posix()] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
    return result


def _build_file_for_project(relative: PurePosixPath, projects: set[str]) -> bool:
    parts = relative.parts
    if parts[:4] == (".lake", "build", "ir", "LeanPool"):
        module = parts[4:]
    elif parts[:5] == (".lake", "build", "lib", "lean", "LeanPool"):
        module = parts[5:]
    else:
        return False
    return bool(module) and any(
        module[0] == name or module[0].startswith(name + ".") for name in projects
    )


def pack(root: Path, base: str, head: str, output: Path) -> None:
    """Store only compiled PR project modules, not the whole 7 GiB pool."""
    projects = _projects(root, base, head)
    manifest = {
        "version": 1,
        "head": head,
        "projects": projects,
        "sources": _source_hashes(root, projects),
        "inputs": {
            name: hashlib.sha256((root / name).read_bytes()).hexdigest()
            for name in PINNED_INPUTS
        },
    }
    payload = json.dumps(manifest, sort_keys=True).encode()
    with tarfile.open(output, "w:gz", compresslevel=1) as archive:
        entry = tarfile.TarInfo(MANIFEST)
        entry.size = len(payload)
        archive.addfile(entry, io.BytesIO(payload))
        for directory in (
            root / ".lake/build/ir/LeanPool",
            root / ".lake/build/lib/lean/LeanPool",
        ):
            if directory.is_dir():
                for path in directory.rglob("*"):
                    relative = PurePosixPath(path.relative_to(root).as_posix())
                    if path.is_file() and _build_file_for_project(
                        relative, set(projects)
                    ):
                        archive.add(path, arcname=relative.as_posix(), recursive=False)


def _restore_build_files(
    root: Path, archive: tarfile.TarFile, members: list[tarfile.TarInfo]
) -> None:
    build_parent = root / ".lake"
    build_parent.mkdir(exist_ok=True)
    # Stage on the destination filesystem, so publication uses atomic renames.
    with tempfile.TemporaryDirectory(
        prefix="lean-project-stage-", dir=build_parent
    ) as name:
        staging = Path(name)
        archive.extractall(staging, members=members, filter="data")
        for entry in members:
            destination = root / entry.name
            destination.parent.mkdir(parents=True, exist_ok=True)
            os.replace(staging / entry.name, destination)


def restore(root: Path, repository: str, run_id: int, previous_head: str) -> None:
    """Download a prior green run's project artifacts and validate before overlay."""
    endpoint = f"repos/{repository}/actions/runs/{run_id}/artifacts?per_page=100"
    artifacts = [
        artifact
        for artifact in github_json(endpoint)["artifacts"]
        if artifact["name"] == ARTIFACT and not artifact["expired"]
    ]
    if not artifacts:
        raise ValueError("prior PR build artifact unavailable")
    artifact_id = max(artifacts, key=lambda artifact: artifact["id"])["id"]
    with tempfile.TemporaryDirectory(prefix="lean-rebase-build-") as temporary:
        zipped = Path(temporary) / "artifact.zip"
        with zipped.open("wb") as output:
            subprocess.run(
                [
                    "gh",
                    "api",
                    f"repos/{repository}/actions/artifacts/{artifact_id}/zip",
                ],
                stdout=output,
                check=True,
                timeout=600,
            )
        with zipfile.ZipFile(zipped) as wrapper:
            if wrapper.namelist() != [ARCHIVE]:
                raise ValueError("unexpected artifact contents")
            with wrapper.open(ARCHIVE) as source:
                archive_path = Path(temporary) / ARCHIVE
                with archive_path.open("wb") as output:
                    shutil.copyfileobj(source, output)
        with tarfile.open(archive_path, "r:gz") as archive:
            member = archive.extractfile(MANIFEST)
            if member is None:
                raise ValueError("missing project build manifest")
            manifest = json.load(member)
            projects = manifest.get("projects")
            if not isinstance(projects, list) or not all(
                isinstance(project, str) and PROJECT.fullmatch(project)
                for project in projects
            ):
                raise ValueError("invalid project build manifest")
            if (
                manifest.get("version") != 1
                or manifest.get("head") != previous_head
                or manifest.get("sources") != _source_hashes(root, projects)
                or manifest.get("inputs")
                != {
                    name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                    for name in PINNED_INPUTS
                }
            ):
                raise ValueError("project build inputs changed")
            members = [
                member for member in archive.getmembers() if member.name != MANIFEST
            ]
            for entry in members:
                relative = PurePosixPath(entry.name)
                if (
                    not entry.isfile()
                    or ".." in relative.parts
                    or not _build_file_for_project(relative, set(projects))
                ):
                    raise ValueError(f"unexpected project artifact: {entry.name}")
            _restore_build_files(root, archive, members)


def restore_new_main_projects(
    root: Path, repository: str, previous: str, base: str, *, missing_only: bool = False
) -> None:
    """Overlay merged PR artifacts before main's own large cache is published."""
    old_base = git(root, "merge-base", previous, base)
    commits = git(
        root, "rev-list", "--first-parent", "--reverse", f"{old_base}..{base}"
    )
    for commit in commits.splitlines():
        parent = git(root, "rev-parse", f"{commit}^1")
        changed = paths(root, parent, commit)
        if not any(
            path.startswith("LeanPool/")
            and path.endswith(".lean")
            and (
                not missing_only
                or not (root / ".lake/build/lib/lean" / path)
                .with_suffix(".olean")
                .is_file()
            )
            for path in changed
        ):
            continue
        try:
            pulls = github_json(f"repos/{repository}/commits/{commit}/pulls")
            for pull in pulls:
                if not pull.get("merged_at"):
                    continue
                head = pull["head"]["sha"]
                run = _successful_run(
                    repository,
                    "lean_action_ci.yml",
                    pull["number"],
                    head,
                    merged=True,
                )
                if run is not None and _has_build_artifact(repository, run["id"]):
                    restore(root, repository, run["id"], head)
                    print(f"Restored merged PR #{pull['number']} project build")
                    break
        except (
            OSError,
            ValueError,
            KeyError,
            subprocess.SubprocessError,
            tarfile.TarError,
        ):
            print(f"No reusable project build for {commit}; Lake will build it")


def main() -> int:
    """Run the eligibility, artifact, or generated-index command."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("decide", "check-index", "pack", "restore", "restore-main")
    )
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", ""))
    parser.add_argument("--workflow", default="lean_action_ci.yml")
    parser.add_argument("--number", type=int, default=0)
    parser.add_argument("--head", default="")
    parser.add_argument("--base", default="")
    parser.add_argument("--run-id", type=int, default=0)
    parser.add_argument("--output", type=Path, default=Path(ARCHIVE))
    args = parser.parse_args()
    root = args.repo_root.resolve()
    if args.command == "decide":
        try:
            print(
                json.dumps(
                    decision(
                        root,
                        args.repository,
                        args.workflow,
                        args.number,
                        args.head,
                        args.base,
                    )
                )
            )
        except (OSError, ValueError, KeyError, subprocess.SubprocessError):
            print(
                json.dumps(
                    {"eligible": False, "reason": "could not verify earlier PR run"}
                )
            )
    elif args.command == "check-index":
        if not check_index(root):
            print("Generated LeanPool.lean is out of date", file=sys.stderr)
            return 1
    elif args.command == "pack":
        pack(root, args.base, args.head, args.output)
    elif args.command == "restore":
        restore(root, args.repository, args.run_id, args.head)
    else:
        restore_new_main_projects(root, args.repository, args.head, args.base)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
