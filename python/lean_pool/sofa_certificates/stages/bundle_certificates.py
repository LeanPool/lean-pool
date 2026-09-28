"""Pack certificates after main growth while retaining their public interfaces."""

import json
import re
from pathlib import Path

from lean_pool import quality
from lean_pool.sofa_certificates.stages.consolidate import rewrite, scoped_lines

IMPORTS = re.compile(r"(?m)^(?:public )?import ([\w.]+)\s*$")
ALIASES = re.compile(
    r"(?m)^(?:/--[^\n]*-/\n)?(?:private )?abbrev \w+\s*:\s*AngleCell\s*:=.*"
    r"(?:\n(?:[ \t].*|\s*))*(?=\n\S|\Z)"
)
HEADER = """/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module
"""


def open_scopes(source: str) -> list[tuple[str, str]]:
    """Recover scopes that Lean would implicitly close at the original EOF."""
    stack = []
    for line in quality._strip_lean_comments(source).splitlines():
        line = re.sub(r"^\s*@\[[^\]]+\]\s*", "", line).strip()
        opening = re.match(
            r"(?:(?:public|private|noncomputable) )?"
            r"(namespace|section)(?:\s+([^\s]+))?",
            line,
        )
        if opening:
            stack.append((opening[1], opening[2] or ""))
        elif re.match(r"end(?:\s|$)", line):
            if not stack:
                raise ValueError("Unbalanced source scope")
            stack.pop()
    return stack


def hoist_aliases(source: str) -> tuple[str, str]:
    """Move closed cell definitions before proofs, preserving qualified names."""
    namespaces = dict(scoped_lines(source))
    hoisted = []
    edits = []
    for match in ALIASES.finditer(source):
        namespace = namespaces[source[: match.start()].count("\n")]
        if not namespace.startswith("GerverSofa.PartE"):
            raise ValueError(f"Unexpected cell namespace: {namespace}")
        hoisted.append(
            "namespace "
            + namespace
            + "\n\n"
            + match[0].rstrip()
            + "\n\nend "
            + namespace
            + "\n"
        )
        edits.append((match.start(), match.end()))
    for start, end in reversed(edits):
        source = source[:start] + source[end:]
    while True:
        reduced = re.sub(r"(?m)^namespace (\S+)\n\s*end \1\n", "", source)
        if reduced == source:
            return "\n".join(hoisted), source
        source = reduced


def fragment(source: str) -> tuple[str, str]:
    """Retain attribution and close module-local scopes around the proof body."""
    source = IMPORTS.sub("", source)
    source = re.sub(r"(?m)^module\s*\n", "", source, 1).strip() + "\n"
    hoisted, source = hoist_aliases(source)
    endings = "".join(
        "\nend" + (" " + name if name else "") + "\n"
        for _, name in reversed(open_scopes(source))
    )
    return hoisted, "section\n\n" + source.rstrip() + "\n" + endings + "\nend\n"


def materialize(modules: list[str], sources: dict[str, str], fragments: dict) -> str:
    """Join a recorded topological group with shared imports and cell definitions."""
    imports = sorted(
        {
            dependency
            for module in modules
            for dependency in IMPORTS.findall(sources[module])
            if dependency not in modules
        }
    )
    source = (
        HEADER
        + "\n"
        + "".join("public import " + name + "\n" for name in imports)
        + "\n/-!\n# Gerver sofa: related certificate and semantic modules\n\n"
        + "\n".join(
            "* `" + name.removeprefix("LeanPool.MovingSofa.") + "`." for name in modules
        )
        + "\n-/\n\n@[expose] public section\n\nnoncomputable section\n\n"
        + "\n".join(fragments[name][0] for name in modules if fragments[name][0])
        + "\n"
        + "\n".join(fragments[name][1] for name in modules)
    )
    source = re.sub(r"end (\S+)\n\nnamespace \1\n", "", source)
    return re.sub(r"\n{3,}", "\n\n", source)


def run(workspace: Path) -> None:
    """Emit the final certificate packing without reading the content checkout."""
    pool = workspace / "pool"
    batches = json.loads((workspace / "final-batch-assignment.json").read_text())
    mapping = json.loads((workspace / "final-module-map.json").read_text())
    selected = {name for batch in batches for name in batch["sources"]}
    paths = {name: pool / (name.replace(".", "/") + ".lean") for name in selected}
    sources = {name: path.read_text() for name, path in paths.items()}
    fragments = {name: fragment(source) for name, source in sources.items()}
    before = sorted(
        item.name for item in quality._declarations_in(list(paths.values()))
    )
    outputs = []
    for batch in batches:
        target = pool / (batch["module"].replace(".", "/") + ".lean")
        if target.exists():
            raise FileExistsError(target)
        source = materialize(batch["sources"], sources, fragments)
        target.write_text(rewrite(source, mapping, IMPORTS))
        outputs.append(target)
    after = sorted(item.name for item in quality._declarations_in(outputs))
    if before != after:
        raise ValueError("Certificate declaration names changed during packing")
    for path in paths.values():
        path.unlink()
