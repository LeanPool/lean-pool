#!/usr/bin/env python3
"""Render the archived Zeta5 certificate templates using exact integer parameters."""

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path

PLACEHOLDER = "{{integer}}"
PROJECT = Path("LeanPool/Zeta5Irrational")


def render(template: str, parameters: list[str]) -> str:
    """Instantiate one proof block, rejecting incomplete or nonnumeric records."""
    if any(re.fullmatch(r"[0-9]+", value) is None for value in parameters):
        raise ValueError("Certificate parameters must be decimal integer strings")
    pieces = template.split(PLACEHOLDER)
    if len(pieces) != len(parameters) + 1:
        raise ValueError("Template and parameter counts differ")
    return (
        "".join(part + number for part, number in zip(pieces, parameters)) + pieces[-1]
    )


def certificate_path(name: str) -> Path:
    """Restrict output to the archived project's Lean modules."""
    path = Path(name)
    if path.is_absolute() or ".." in path.parts or path.suffix != ".lean":
        raise ValueError(f"Invalid certificate path: {name}")
    if not path.is_relative_to(PROJECT):
        raise ValueError(f"Certificate outside the project: {name}")
    return path


def _render_modules(archive: Path) -> dict[Path, bytes]:
    """Validate and render every recorded module before touching output."""
    manifest = json.loads((archive / "manifest.json").read_text(encoding="utf-8"))
    modules = {}
    for name, specification in manifest["files"].items():
        relative = certificate_path(name)
        records = json.loads(
            (archive / "records" / specification["records"]).read_text(encoding="utf-8")
        )
        blocks = []
        for template, parameters in records:
            if re.fullmatch(r"[0-9]{3}", template) is None:
                raise ValueError("Invalid template identifier")
            source = (archive / "templates" / f"{template}.txt").read_text(
                encoding="utf-8"
            )
            blocks.append(render(source, parameters))
        modules[relative] = "".join(blocks).encode("utf-8")
    return modules


def regenerate(archive: Path, destination: Path, check: bool) -> int:
    """Check a checkout or write prevalidated modules to an exclusively new tree."""
    modules = _render_modules(archive)
    if check:
        mismatches = [
            str(path)
            for path, content in modules.items()
            if not (destination / path).is_file()
            or (destination / path).read_bytes() != content
        ]
        if mismatches:
            raise ValueError("Certificates differ: " + ", ".join(mismatches))
        return len(modules)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.mkdir(mode=0o700)
    try:
        for path, content in modules.items():
            target = destination / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
    except BaseException:
        shutil.rmtree(destination)
        raise
    return len(modules)


def verify_archive(archive: Path) -> None:
    """Check baseline hashes independently of a target checkout."""
    manifest = json.loads((archive / "manifest.json").read_text(encoding="utf-8"))
    for path, content in _render_modules(archive).items():
        if (
            hashlib.sha256(content).hexdigest()
            != manifest["files"][path.as_posix()]["sha256"]
        ):
            raise ValueError("Archived certificate differs from its pinned source hash")


def main() -> None:
    """Run generation, checkout comparison, or baseline archive verification."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--archive", type=Path, default=Path(__file__).parent / "archive"
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--output", type=Path, help="Write generated modules beneath this directory"
    )
    mode.add_argument(
        "--check", type=Path, help="Compare generated modules with this checkout"
    )
    mode.add_argument("--verify-archive", action="store_true")
    arguments = parser.parse_args()
    if arguments.verify_archive:
        verify_archive(arguments.archive)
        print("Archive matches every pinned certificate hash")
    else:
        count = regenerate(
            arguments.archive,
            arguments.check or arguments.output,
            arguments.check is not None,
        )
        print(
            f"{'Checked' if arguments.check else 'Generated'} {count} certificate modules"
        )


if __name__ == "__main__":
    main()
