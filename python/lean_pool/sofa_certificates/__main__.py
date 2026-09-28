"""Reproduce the moving-sofa Part E certificate modules from pinned inputs."""

import argparse
import hashlib
import importlib
import json
import logging
import re
import shutil
import time
from pathlib import Path
from tarfile import open as open_tar

DATA = Path(__file__).parent / "data"
ARCHIVE_SHA256 = "88538a166208cdb7ba2c4079a296c8d7becf18758c9b4540750d81b271e79f70"
ARCHIVE_PREFIX = (
    "MovingSofa-4d5569131940815f47a9ccf3e90a4c5043c56127/vendor/gerver-sofa/"
)
PROJECT = Path("LeanPool/MovingSofa")
CERTIFICATES = PROJECT / "GerverSofa/KernelOnly/PartE/Certificates"
STAGES = (
    "split_proofs",
    "share_cells",
    "normalize",
    "rename",
    "module_names",
    "wrap",
    "split_reconstruction",
    "expand",
    "special_cover",
    "consolidate",
    "repair_roots",
    "wrap_roots",
    "public_root",
    "separate_joins",
    "bundle_certificates",
)


def digest(content: bytes) -> str:
    """Return the content's SHA-256 digest."""
    return hashlib.sha256(content).hexdigest()


def validate_leaves(leaves: dict[str, int], depth: int) -> None:
    """Reject incomplete, overlapping or incorrectly labelled cover trees."""
    if not leaves:
        raise ValueError("Empty cover")
    nodes = {""}
    for path, remaining in leaves.items():
        if re.fullmatch("[0-3]*", path) is None or remaining != depth - len(path):
            raise ValueError("Invalid cover path or remaining depth")
        if remaining < 0:
            raise ValueError("Cover exceeds its depth")
        nodes.update(path[:index] for index in range(1, len(path) + 1))
    for path in nodes:
        children = {path + str(index) for index in range(4)}
        if path in leaves:
            if children & nodes:
                raise ValueError("Overlapping cover leaves")
        elif not children <= nodes:
            raise ValueError("Incomplete cover")


def validate_witnesses() -> None:
    """Check every recorded tree before emitting any proof source."""
    candidates = json.loads((DATA / "cover-expansion-candidates.json").read_text())
    trees = {}
    for line in (DATA / "cover-bulk-discovery.jsonl").read_text().splitlines():
        identity, path, depth, reason = line.split("|")
        tree = trees.setdefault(int(identity), {})
        if reason != "rejected" or path in tree:
            raise ValueError("Invalid or duplicate cover witness")
        tree[path] = int(depth)
    if set(trees) != {item["id"] for item in candidates}:
        raise ValueError("Cover candidate IDs do not match the witnesses")
    for item in candidates:
        validate_leaves(trees[item["id"]], item["depth"])
    special = {}
    for line in (DATA / "cover-special-discovery.txt").read_text().splitlines():
        marker, path, depth, reason = line.split("|")
        if marker != "COVER" or reason != "rejected" or path in special:
            raise ValueError("Invalid special-cover witness")
        special[path] = int(depth)
    validate_leaves(special, 9)


def prepare_source(source: str) -> str:
    """Apply the import's visibility, module prefix and attribution headers."""
    source = re.sub(
        r"^(?:public )?import\s+([\w.]+)",
        lambda match: (
            "public import "
            + (
                "LeanPool.MovingSofa." + match[1]
                if match[1].startswith(("GerverSofa.", "LeanCert."))
                else match[1]
            )
        ),
        source,
        flags=re.M,
    )
    header = (
        "/-\nCopyright (c) 2026 Dawid Trela. All rights reserved.\n"
        "Released under MIT license as described in the file LICENSE.\n"
        "Authors: Dawid Trela\n-/\nmodule\n\n"
    )
    source = header + source
    imports = list(re.finditer(r"^public import[^\n]*\n", source, re.M))
    if imports:
        index = imports[-1].end()
        source = source[:index] + "\n@[expose] public section\n" + source[index:]
    return source


def read_sources(archive: Path) -> dict[str, str]:
    """Read only checksum-pinned source members without extracting archive paths."""
    if digest(archive.read_bytes()) != ARCHIVE_SHA256:
        raise ValueError("Upstream release archive SHA-256 mismatch")
    manifest = json.loads((DATA / "inputs.json").read_text())
    sources = {}
    with open_tar(archive) as zipped:
        for module, expected in manifest.items():
            if re.fullmatch(r"GerverSofa\.KernelOnly\.PartE\.[\w.]+", module) is None:
                raise ValueError("Unexpected upstream module name")
            member = ARCHIVE_PREFIX + module.replace(".", "/") + ".lean"
            handle = zipped.extractfile(member)
            if handle is None:
                raise ValueError(f"Missing source: {module}")
            content = handle.read()
            if digest(content) != expected:
                raise ValueError(f"Upstream source SHA-256 mismatch: {module}")
            sources[module] = content.decode("utf-8")
    return sources


def verify_outputs(
    folder: Path, manifest: Path = DATA / "outputs.json"
) -> dict[str, str]:
    """Require the exact expected file set and all expected source digests."""
    expected = json.loads(manifest.read_text())
    for entry in folder.iterdir():
        if entry.is_dir() or entry.is_symlink():
            raise ValueError(f"Unexpected directory or symbolic link: {entry.name}")
    actual = {path.name: digest(path.read_bytes()) for path in folder.glob("*.lean")}
    if actual != expected:
        changed = sorted(
            name
            for name in actual.keys() | expected.keys()
            if actual.get(name) != expected.get(name)
        )
        raise ValueError(f"Reproduction mismatch: {changed}")
    return actual


def reproduce(archive: Path, workspace: Path) -> None:
    """Run the source pipeline in a new directory, refusing existing output."""
    started = time.monotonic()
    sources = read_sources(archive)
    validate_witnesses()
    workspace.mkdir(parents=True, exist_ok=False)
    for resource in DATA.iterdir():
        shutil.copyfile(resource, workspace / resource.name)
    for module, source in sources.items():
        target = workspace / "pool" / PROJECT / (module.replace(".", "/") + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(prepare_source(source))
    for name in STAGES:
        if name == "bundle_certificates":
            for path in (workspace / "pool" / CERTIFICATES).glob("*.lean"):
                path.write_text(path.read_text().rstrip() + "\n")
            verify_outputs(
                workspace / "pool" / CERTIFICATES, DATA / "intermediate-outputs.json"
            )
        print(f"Running {name}", flush=True)
        stage = importlib.import_module(f"lean_pool.sofa_certificates.stages.{name}")
        stage.run(workspace)
    folder = workspace / "pool" / CERTIFICATES
    for path in folder.glob("*.lean"):
        path.write_text(path.read_text().rstrip() + "\n")
    hashes = verify_outputs(folder)
    report = {
        "archive_sha256": ARCHIVE_SHA256,
        "files": hashes,
        "wall_seconds": time.monotonic() - started,
    }
    (workspace / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified {len(hashes)} byte-identical certificate modules in {folder}")


def main() -> None:
    """Run a fresh reproduction or verify an existing certificate directory."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate = commands.add_parser("generate")
    generate.add_argument("--archive", type=Path, required=True)
    generate.add_argument("--workspace", type=Path, required=True)
    verify = commands.add_parser("verify")
    verify.add_argument("directory", type=Path)
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    if arguments.command == "generate":
        reproduce(arguments.archive.resolve(), arguments.workspace.resolve())
    else:
        print(
            f"Verified {len(verify_outputs(arguments.directory))} certificate modules"
        )


if __name__ == "__main__":
    main()
