"""Run resumable Lean/Mathlib migrations on the Lean VM's cx account pool."""

from __future__ import annotations

import argparse
import fcntl
import json
import logging
import math
import os
import re
import shutil
import subprocess
from datetime import UTC, datetime
from pathlib import Path

from lean_pool.bump import current_version, newer_versions, pin_files, remote_tags

LOGGER = logging.getLogger(__name__)
REPOSITORY = "LeanPool/lean-pool"
REMOTE = f"https://github.com/{REPOSITORY}.git"
PINS = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "docbuild/lean-toolchain",
    "docbuild/lakefile.toml",
    "docbuild/lake-manifest.json",
)
GATES = {
    "indexes": ["lake", "exe", "mk_all", "--check"],
    "linter": ["lake", "exe", "runLinter", "LeanPool"],
    "style": ["lake", "exe", "lint-style", "LeanPool"],
    "quality": [
        "uv",
        "run",
        "--directory",
        "python",
        "--locked",
        "python",
        "-m",
        "lean_pool.quality",
        "--repo",
        "..",
    ],
}
WARNING = re.compile(r"(^|: )warning:", re.M)


def rank_accounts(statuses: list[dict]) -> list[str]:
    """Prefer most remaining quota in the most constrained reported window."""
    eligible = []
    for status in statuses:
        used = status.get("usedPercent")
        if (
            status.get("provider") not in (None, "openai")
            or status.get("name") == "claude"
            or not all(
                status.get(key)
                for key in ("ready", "authenticated", "identityOk", "available")
            )
            or not isinstance(used, (int, float))
            or not math.isfinite(used)
            or not 0 <= used < 98
            or not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", status.get("name", ""))
        ):
            continue
        eligible.append((used, status["name"]))
    return [name for _, name in sorted(eligible)]


def save(path: Path, value: dict) -> None:
    """Replace a private checkpoint atomically."""
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


class Runner:
    """Own one persistent checkout, checkpoint, and set of private logs."""

    def __init__(self, root: Path) -> None:
        """Keep mutable run data outside the installed controller."""
        self.root = root
        self.repository = root / "repository"
        self.state_path = root / "pending.json"
        self.state = (
            json.loads(self.state_path.read_text()) if self.state_path.exists() else {}
        )
        self.environment = os.environ.copy()
        for key in list(self.environment):
            if key.startswith(("OPENAI_", "AZURE_OPENAI_", "ANTHROPIC_")):
                self.environment.pop(key)
        self.environment["LEAN_NUM_THREADS"] = "2"

    def command(self, *arguments: str, directory: Path | None = None) -> str:
        """Run a controller command and retain ordinary error diagnostics."""
        result = subprocess.run(
            arguments,
            cwd=directory or self.repository,
            env=self.environment,
            text=True,
            stdout=subprocess.PIPE,
            check=True,
        )
        return result.stdout.strip()

    def logged(self, arguments: list[str], name: str, prompt: str | None = None) -> int:
        """Keep compiler and agent transcripts private, outside the checkout."""
        path = self.root / "logs" / name
        LOGGER.info("Running %s; log: %s", arguments[0], path)
        with path.open("w") as output:
            return subprocess.run(
                arguments,
                cwd=self.repository,
                env=self.environment,
                input=prompt,
                text=True,
                stdout=output,
                stderr=subprocess.STDOUT,
            ).returncode

    def checkpoint(self, **values: object) -> None:
        """Record progress before each interruptible operation."""
        self.state.update(values)
        save(self.state_path, self.state)

    def changed_paths(self) -> list[str]:
        """Include untracked agent edits when enforcing the write scope."""
        tracked = self.command("git", "diff", "--name-only", "-z", "HEAD")
        untracked = self.command(
            "git", "ls-files", "--others", "--exclude-standard", "-z"
        )
        return [path for path in (tracked + "\0" + untracked).split("\0") if path]

    def commit_repairs(self, project: str) -> None:
        """Preserve partial progress, refusing any edit outside this project."""
        paths = self.changed_paths()
        for path in paths:
            allowed = path == f"LeanPool/{project}.lean" or (
                path.startswith(f"LeanPool/{project}/") and path.endswith(".lean")
            )
            if not allowed or (self.repository / path).is_symlink():
                raise RuntimeError(f"repair changed an unexpected path: {path}")
        if paths:
            self.command("git", "add", "--", *paths)
            self.command(
                "git", "commit", "-m", f"Repair {project} for {self.state['target']}"
            )

    def update_pins(self) -> None:
        """Finish pin updates before a restart can merge more upstream work."""
        target = self.state["target"]
        if self.command("git", "branch", "--show-current") != f"bump/{target}":
            raise RuntimeError("interrupted pin checkout changed branches")
        if set(self.changed_paths()) - set(PINS):
            raise RuntimeError("unexpected edits during dependency update")
        self.checkpoint(phase="pins")
        pin_files(self.repository, target)
        self.command("lake", "update", "mathlib")
        self.command(
            "lake", "update", "doc-gen4", directory=self.repository / "docbuild"
        )
        self.command("git", "add", "--", *PINS)
        if self.command("git", "diff", "--cached", "--name-only"):
            self.command(
                "git", "commit", "-m", f"chore: pin Lean and Mathlib to {target}"
            )
        self.checkpoint(phase="cache")

    def checkout(self) -> None:
        """Fetch complete ancestry so resuming a branch can merge current main."""
        if not self.repository.exists():
            self.command(
                "git", "clone", REMOTE, str(self.repository), directory=self.root
            )
        if self.command("git", "remote", "get-url", "origin") != REMOTE:
            raise RuntimeError("the bump checkout has an unexpected origin")
        if self.command("git", "rev-parse", "--is-shallow-repository") == "true":
            self.command("git", "fetch", "--unshallow", "origin")
        self.command("git", "config", "user.name", "Lean Pool version bump")
        self.command(
            "git",
            "config",
            "user.email",
            "41898282+github-actions[bot]@users.noreply.github.com",
        )
        if self.state.get("phase") == "pins":
            self.update_pins()
        if self.state.get("project"):
            expected = f"bump/{self.state['target']}"
            if self.command("git", "branch", "--show-current") != expected:
                raise RuntimeError("interrupted repair checkout changed branches")
            self.commit_repairs(self.state["project"])
            self.checkpoint(project=None)
        if self.changed_paths():
            raise RuntimeError(
                "preserving unexpected uncommitted changes in the bump checkout"
            )
        self.command(
            "git",
            "fetch",
            "--prune",
            "origin",
            "+refs/heads/*:refs/remotes/origin/*",
        )

    def select_target(self, requested: str | None, stable_only: bool) -> str | None:
        """Resume pending work before detecting another upstream release."""
        if self.state.get("target"):
            if requested and requested != self.state["target"]:
                raise RuntimeError(
                    "finish the pending target before selecting another release"
                )
            return self.state["target"]
        self.command("git", "checkout", "--detach", "origin/main")
        available = newer_versions(
            current_version(self.repository), remote_tags(), stable_only=stable_only
        )
        if requested and requested not in available:
            raise RuntimeError(
                "requested target must be a published newer Mathlib release"
            )
        target = requested or (available[-1] if available else None)
        if target:
            self.checkpoint(target=target)
        return target

    def prepare_branch(self, target: str) -> None:
        """Keep local and remote repairs without resetting or force-pushing."""
        branch = f"bump/{target}"
        branches = self.command(
            "git", "for-each-ref", "--format=%(refname)"
        ).splitlines()
        if f"refs/heads/{branch}" in branches:
            self.command("git", "checkout", branch)
        elif f"refs/remotes/origin/{branch}" in branches:
            self.command("git", "checkout", "-b", branch, f"origin/{branch}")
        else:
            self.command("git", "checkout", "-b", branch, "origin/main")
        if f"refs/remotes/origin/{branch}" in branches:
            self.command("git", "merge", "--no-edit", f"origin/{branch}")
        self.command("git", "merge", "--no-edit", "origin/main")
        self.update_pins()
        self.command("git", "push", "origin", branch)
        self.command("lake", "exe", "cache", "get")

    def build_project(self, project: str) -> bool:
        """Build every source through its public Imports module, including warnings."""
        entry = self.repository / "LeanPool" / project / "Imports.lean"
        module = f"LeanPool.{project}" + (".Imports" if entry.exists() else "")
        name = f"build-{project}.log"
        status = self.logged(["lake", "build", module], name)
        return status == 0 and not WARNING.search(
            (self.root / "logs" / name).read_text()
        )

    def repair(self, project: str) -> None:
        """Try each eligible cx account once, retaining edits across failures."""
        tried: set[str] = set()
        self.checkpoint(project=project)
        while True:
            statuses = json.loads(self.command("cx", "limits", "--json"))
            candidates = [name for name in rank_accounts(statuses) if name not in tried]
            if not candidates:
                raise RuntimeError(
                    "cx waterfall exhausted; checkpoint retained for retry"
                )
            account = candidates[0]
            tried.add(account)
            LOGGER.info("Repairing %s using cx %s", project, account)
            before = self.command("git", "rev-parse", "HEAD")
            status = self.logged(
                self.agent_arguments(account),
                f"repair-{project}-{account}.log",
                self.prompt(project),
            )
            if self.command("git", "rev-parse", "HEAD") != before:
                raise RuntimeError("repair agent unexpectedly changed Git history")
            self.commit_repairs(project)
            if self.build_project(project):
                self.checkpoint(project=None)
                return
            LOGGER.warning(
                "cx %s exited %s; %s still needs repair", account, status, project
            )

    def agent_arguments(self, account: str) -> list[str]:
        """Use cx credentials while keeping the repair agent inside its workspace."""
        return [
            "cx",
            account,
            "exec",
            "--ignore-user-config",
            "--sandbox",
            "workspace-write",
            "-c",
            'approval_policy="never"',
            "-c",
            "sandbox_workspace_write.network_access=true",
            "--add-dir",
            "/data/.elan",
            "--add-dir",
            "/data/codex/cache/shared",
            "--model",
            os.environ.get("LEAN_POOL_BUMP_MODEL", "gpt-6.1-sol"),
            "-c",
            'model_reasoning_effort="xhigh"',
            "--cd",
            str(self.repository),
            "-",
        ]

    def prompt(self, project: str) -> str:
        """Reconcile a previous attempt using the same files and fresh diagnostics."""
        diagnostics = (self.root / "logs" / f"build-{project}.log").read_text()
        return f"""Repair LeanPool.{project} for {self.state["target"]}.
Earlier attempts may have left partial repairs. Inspect the files and Git history
and continue their work. Read .claude/skills/version-bump-project/SKILL.md and follow
its proof, statement-preservation and no-waiver constraints. Edit only
LeanPool/{project}/**/*.lean and LeanPool/{project}.lean if it exists.
Use CLI Lake/Lean and rg; do not delegate to other agents. Do not commit, push,
open a PR, change branches, or modify any other files. Do not weaken statements,
drop declarations, change checks or increase resource limits. The controller handles
checkpoints, commits, whole-pool validation and the draft PR.
Build LeanPool.{project}.Imports if that module exists, otherwise LeanPool.{project}.
Finish when that build has zero errors and warnings; report unresolved issues honestly.
Diagnostics are supplied below instead of diagnostics.txt.
Current build diagnostics (excerpt):
{diagnostics[-24000:]}
"""

    def validate(self) -> dict[str, bool]:
        """Run the full build and every existing gate independently of the agent."""
        self.checkpoint(phase="validation")
        status = self.logged(["lake", "build", "LeanPool"], "whole-pool.log")
        results = {
            "build": status == 0
            and not WARNING.search((self.root / "logs" / "whole-pool.log").read_text())
        }
        for name, arguments in GATES.items():
            results[name] = (
                self.logged(arguments, f"gate-{name}.log") == 0
                if results["build"]
                else False
            )
        return results

    def pull_request_body(
        self, revision: str, results: dict[str, bool], incomplete: bool
    ) -> Path:
        """Report measured validation at the precise commit being published."""
        rows = "\n".join(
            f"| {name} | {'pass' if passed else 'FAIL / not run'} |"
            for name, passed in results.items()
        )
        body = self.root / "pull-request.md"
        body.write_text(
            f"Automated migration to `{self.state['target']}`, run on the Lean VM.\n\n"
            f"Validation at `{revision}`:\n\n| Check | Result |\n|---|---|\n{rows}\n\n"
            + (
                "Repair is incomplete; saved progress will be retried.\n\n"
                if incomplete
                else ""
            )
            + "Review statement changes before marking ready. "
            "Required CI must pass on the current head. "
            "Execution logs and cx account data remain private on the VM.\n"
        )
        return body

    def publish(self, results: dict[str, bool], incomplete: bool = False) -> None:
        """Publish a draft with measured results; a racing push fails safely."""
        branch = f"bump/{self.state['target']}"
        self.command("git", "push", "origin", branch)
        revision = self.command("git", "rev-parse", "HEAD")
        body = self.pull_request_body(revision, results, incomplete)
        pulls = json.loads(
            self.command(
                "gh",
                "pr",
                "list",
                "--repo",
                REPOSITORY,
                "--head",
                branch,
                "--state",
                "open",
                "--json",
                "number",
            )
        )
        if pulls:
            self.command(
                "gh",
                "pr",
                "edit",
                str(pulls[0]["number"]),
                "--repo",
                REPOSITORY,
                "--body-file",
                str(body),
            )
        else:
            self.command(
                "gh",
                "pr",
                "create",
                "--repo",
                REPOSITORY,
                "--draft",
                "--base",
                "main",
                "--head",
                branch,
                "--title",
                f"chore: bump Lean and Mathlib to {self.state['target']}",
                "--body-file",
                str(body),
            )

    def run(self, requested: str | None, stable_only: bool, probe_only: bool) -> None:
        """Keep the migration pending until every gate passes."""
        self.checkout()
        target = self.select_target(requested, stable_only)
        if not target:
            LOGGER.info("Pool already tracks the newest Mathlib release")
            return
        self.prepare_branch(target)
        self.checkpoint(phase="probe")
        projects = sorted(
            {
                path.parent.name
                for path in (self.repository / "LeanPool").glob("*/Imports.lean")
            }
        )
        if not projects:
            raise RuntimeError("no project Imports modules found")
        for project in projects:
            if not self.build_project(project) and not probe_only:
                try:
                    self.repair(project)
                except RuntimeError:
                    self.publish({"build": False}, incomplete=True)
                    raise
                self.command("git", "push", "origin", f"bump/{target}")
        results = self.validate()
        self.publish(results)
        if not all(results.values()):
            raise RuntimeError("migration has failing gates; checkpoint retained")
        self.state["phase"] = "complete"
        save(self.root / "completed.json", self.state)
        self.state_path.unlink()
        LOGGER.info("Migration validated and draft PR published")


def main() -> None:
    """Serialize timer/manual activations and keep all runtime files private."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("/data/lean-pool-bump"))
    parser.add_argument("--version")
    parser.add_argument("--stable-only", action="store_true")
    parser.add_argument("--probe-only", action="store_true")
    arguments = parser.parse_args()
    os.umask(0o077)
    root = arguments.root.resolve()
    root.mkdir(parents=True, exist_ok=True, mode=0o700)
    (root / "logs").mkdir(exist_ok=True)
    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s"
    )
    with (root / "run.lock").open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            LOGGER.info("A version bump is already running")
            return
        if shutil.disk_usage(root).free < 30 * 1024**3:
            raise RuntimeError("version bump needs at least 30 GiB free")
        LOGGER.info("Starting activation at %s", datetime.now(UTC).isoformat())
        Runner(root).run(arguments.version, arguments.stable_only, arguments.probe_only)


if __name__ == "__main__":
    main()
