"""Render API documentation for every independent project and verify coverage."""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

from lean_pool.indexes import project_modules, structure_errors


def documentation_roots(root: Path) -> list[str]:
    """Select complete public project roots without changing the fixed pool root."""
    errors = structure_errors(root)
    if errors:
        path, message = errors[0]
        raise ValueError(f"{path}: {message}")
    projects = project_modules(root)
    if not projects:
        raise ValueError("no LeanPool projects found")
    return [
        "LeanPool",
        *(f"LeanPool.{project}.Imports" for project in projects),
        "Init",
        "Std",
        "Lake",
        "Lean",
    ]


def validate_site(root: Path, site: Path) -> None:
    """Reject a root-only site or any missing page for a compiled pool source."""
    sources = [root / "LeanPool.lean", *sorted((root / "LeanPool").rglob("*.lean"))]
    required = [
        site / "index.html",
        site / "declarations/declaration-data.bmp",
        *(site / path.relative_to(root).with_suffix(".html") for path in sources),
    ]
    missing = [
        path.relative_to(site)
        for path in required
        if not path.is_file() or not path.stat().st_size
    ]
    if missing:
        sample = ", ".join(str(path) for path in missing[:5])
        raise ValueError(
            f"documentation is missing {len(missing)} required pages/files: {sample}"
        )


def build_site(root: Path, lake: Path) -> None:
    """Generate HTML from verified docInfo using every project's import closure."""
    roots = documentation_roots(root)
    # doc-gen4's library docs facet follows only library roots. LeanPool's fixed
    # root imports no projects, so supply their public roots to fromDb directly.
    subprocess.run(
        [
            str(lake),
            "exe",
            "doc-gen4",
            "fromDb",
            "--build",
            ".lake/build",
            "--manifest",
            ".lake/build/doc-manifest.json",
            ".lake/build/api-docs.db",
            *roots,
        ],
        cwd=root / "docbuild",
        check=True,
    )
    validate_site(root, root / "docbuild/.lake/build/doc")


def main(argv: list[str] | None = None) -> int:
    """Build the complete site or verify an existing documentation artifact."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("build", "validate"))
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--lake", type=Path, default=Path.home() / ".elan/bin/lake")
    arguments = parser.parse_args(argv)
    root = arguments.repo.resolve()
    if arguments.command == "build":
        build_site(root, arguments.lake.expanduser().resolve())
    else:
        documentation_roots(root)
        validate_site(root, root / "docbuild/.lake/build/doc")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
