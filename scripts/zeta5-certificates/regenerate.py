#!/usr/bin/env python3
"""Render the archived Zeta5 certificate templates using exact integer parameters."""

import argparse
import hashlib
import json
import re
import tempfile
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


def _render_into(archive: Path, destination: Path, check: bool) -> int:
    """Render every module and either write it or compare it with a checkout."""
    manifest = json.loads((archive / "manifest.json").read_text())
    mismatches = []
    for name, specification in manifest["files"].items():
        relative = certificate_path(name)
        records = json.loads(
            (archive / "records" / specification["records"]).read_text()
        )
        blocks = []
        for template, parameters in records:
            if re.fullmatch(r"[0-9]{3}", template) is None:
                raise ValueError("Invalid template identifier")
            source = (archive / "templates" / f"{template}.txt").read_text()
            blocks.append(render(source, parameters))
        content = "".join(blocks).encode()
        target = destination / relative
        if check:
            if not target.is_file() or target.read_bytes() != content:
                mismatches.append(name)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
    if mismatches:
        raise ValueError("Certificates differ: " + ", ".join(mismatches))
    return len(manifest["files"])


def regenerate(archive: Path, destination: Path, check: bool) -> int:
    """Check a checkout or publish a complete generation to a new directory."""
    if check:
        return _render_into(archive, destination, True)
    if destination.exists() or destination.is_symlink():
        raise FileExistsError("Generation requires a new output directory")
    with tempfile.TemporaryDirectory(
        prefix=".zeta5-certificates-", dir=destination.parent
    ) as staging_name:
        staging = Path(staging_name)
        count = _render_into(archive, staging, False)
        staging.rename(destination)
    return count


def verify_archive(archive: Path) -> None:
    """Check the immutable baseline hashes independently of a target checkout."""
    manifest = json.loads((archive / "manifest.json").read_text())
    for specification in manifest["files"].values():
        records = json.loads(
            (archive / "records" / specification["records"]).read_text()
        )
        content = "".join(
            render((archive / "templates" / f"{name}.txt").read_text(), parameters)
            for name, parameters in records
        ).encode()
        if hashlib.sha256(content).hexdigest() != specification["sha256"]:
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
