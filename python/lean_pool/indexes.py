"""Generate and validate complete project aggregates without a Lean toolchain."""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

from lean_pool.exposition.source_text import code_view

MODULE_HEADER = "module  -- shake: keep-all --deprecated_module: ignore\n\n"
AGGREGATE_NAME = "Imports.lean"
GENERATED_MARKER = "-- Generated project imports; run `lake exe mk_all`.\n"
AGGREGATE_HEADER = (
    "/-\nCopyright (c) 2026 Lean Pool contributors. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: Lean Pool contributors\n-/\n" + MODULE_HEADER + GENERATED_MARKER
)
# Production module-system packages must never revert to a flat index.
REQUIRE_PROJECT_ROOTS = True


def project_modules(root: Path) -> dict[str, list[str]]:
    """Group all source modules by their first component below LeanPool."""
    pool = root / "LeanPool"
    projects: dict[str, list[str]] = {}
    for path in sorted(pool.rglob("*.lean")):
        relative = path.relative_to(pool)
        if len(relative.parts) == 2 and path.name == AGGREGATE_NAME:
            continue
        project = relative.parts[0].removesuffix(".lean")
        module = "LeanPool." + ".".join(relative.with_suffix("").parts)
        projects.setdefault(project, []).append(module)
    return {project: sorted(modules) for project, modules in sorted(projects.items())}


def has_project_roots(root: Path) -> bool:
    """Detect the migrated layout, including a damaged or conflicted index."""
    return any((root / "LeanPool").glob(f"*/{AGGREGATE_NAME}"))


def requires_project_roots(root: Path) -> bool:
    """Require the new layout for module-system repositories after migration."""
    if has_project_roots(root):
        return True
    config = root / "lakefile.toml"
    return (
        REQUIRE_PROJECT_ROOTS
        and config.exists()
        and tomllib.loads(config.read_text(encoding="utf-8")).get(
            "requiresModuleSystem"
        )
        is True
    )


def render_project_indexes(root: Path) -> dict[Path, str]:
    """Render exactly one public aggregate per project and a small pool index."""
    projects = project_modules(root)
    result = {
        root / "LeanPool" / project / AGGREGATE_NAME: AGGREGATE_HEADER
        + "".join(f"public import {module}\n" for module in modules)
        for project, modules in projects.items()
    }
    result[root / "LeanPool.lean"] = MODULE_HEADER + "".join(
        f"public import LeanPool.{project}.Imports\n" for project in projects
    )
    return result


def structure_errors(root: Path) -> list[tuple[Path, str]]:
    """Reject missing, duplicate, private, stale or cross-project index imports."""
    expected = render_project_indexes(root)
    errors = []
    for path, content in expected.items():
        if not path.exists():
            errors.append((path, "missing generated project index"))
        elif path.read_text(encoding="utf-8") != content:
            errors.append(
                (
                    path,
                    "project index must list every source exactly once "
                    "using sorted public imports",
                )
            )
    for path in (root / "LeanPool").glob(f"*/{AGGREGATE_NAME}"):
        if path not in expected:
            errors.append((path, "project aggregate has no project source files"))
    return errors


def _generated_aggregate(source: str) -> bool:
    """Recognize import-only generated roots, including current merge conflicts."""
    if GENERATED_MARKER not in source:
        return False
    code = code_view(source)
    return all(
        not line.strip()
        or re.fullmatch(r"\s*module\s*", line)
        or re.fullmatch(r"\s*(?:public\s+)?import\s+[\w'.]+\s*", line)
        or re.match(r"^(?:<<<<<<<|=======|>>>>>>>|\|{7})(?:\s|$)", line)
        for line in code.splitlines()
    )


def _write_indexes(contents: dict[Path, str], *, check: bool) -> int:
    """Check indexes or update them without overwriting a mathematical source."""
    for path in contents:
        if path.name == AGGREGATE_NAME and path.exists():
            if not _generated_aggregate(path.read_text(encoding="utf-8")):
                raise ValueError(f"refusing to overwrite source file {path}")
    changed = 0
    for path, content in contents.items():
        previous = path.read_text(encoding="utf-8") if path.exists() else None
        if previous == content:
            continue
        changed += 1
        if check:
            print(f"{path} is missing or out of date; run `lake exe mk_all`")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
            print(f"Updated {path}")
    return min(changed, 125) if check else 0


def _library_index(root: Path, library: str, *, use_module: bool) -> str:
    """Keep the ordinary flat indexes for Challenge and Solution unchanged."""
    existing = root / f"{library}.lean"
    source = existing.read_text(encoding="utf-8") if existing.exists() else ""
    module_style = use_module or code_view(source).lstrip().startswith("module")
    prefix = "public " if module_style else ""
    modules = sorted(
        library + "." + ".".join(path.relative_to(root / library).with_suffix("").parts)
        for path in (root / library).rglob("*.lean")
    )
    return (MODULE_HEADER if module_style else "") + "".join(
        f"{prefix}import {module}\n" for module in modules
    )


def main(argv: list[str] | None = None) -> int:
    """Provide the local mk_all CLI, shared with mechanical PR rebases."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path("."))
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--module", action="store_true")
    parser.add_argument("--project-roots", action="store_true")
    parser.add_argument("--lib", choices=("LeanPool", "Challenge", "Solution"))
    args = parser.parse_args(argv)
    root = args.repo.resolve()
    contents = {}
    for library in [args.lib] if args.lib else ["LeanPool", "Challenge", "Solution"]:
        if library == "LeanPool" and (
            args.project_roots or requires_project_roots(root)
        ):
            contents.update(render_project_indexes(root))
        else:
            contents[root / f"{library}.lean"] = _library_index(
                root, library, use_module=args.module
            )
    try:
        return _write_indexes(contents, check=args.check)
    except ValueError as error:
        print(error, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
