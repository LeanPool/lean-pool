"""Rename."""

import json
import logging
import re

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    pool = r / "pool"
    project = pool / "LeanPool/MovingSofa"
    base = project / "GerverSofa/KernelOnly/PartE"
    renames = {}
    paths = {}
    for p in base.glob("E24KC5*.lean"):
        m = re.fullmatch(
            (
                "E24KC5(Direct|Join)_e24KC2(PhiAbove|PhiBelow|Theta"
                "Above|ThetaBelow)Leaf.+_(\\d+)\\.lean"
            ),
            p.name,
        )
        if not m:
            continue
        q = base / m[2] / (("Leaf" if m[1] == "Direct" else "Join") + m[3] + ".lean")
        assert not q.exists()
        assert q not in paths.values()
        paths[p] = q
        renames[str(p.relative_to(pool).with_suffix("")).replace("/", ".")] = str(
            q.relative_to(pool).with_suffix("")
        ).replace("/", ".")
    identifiers = set()
    for p in base.glob("*.lean"):
        identifiers.update(re.findall("\\b[A-Za-z][A-Za-z0-9_]*\\b", p.read_text()))
    replacements = {i: re.sub("_+", "_", i) for i in identifiers if "__" in i}
    assert len(set(replacements.values())) == len(replacements)
    assert not set(replacements.values()) & identifiers - set(replacements)
    imports = re.compile("(?m)^(public import )(\\S+)$")
    identifier = re.compile("\\b[A-Za-z][A-Za-z0-9_]*\\b")
    for p in project.rglob("*.lean"):
        s = p.read_text()
        t = imports.sub(lambda m: m[1] + renames.get(m[2], m[2]), s)
        if base in p.parents:
            t = identifier.sub(lambda m: replacements.get(m[0], m[0]), t)
        if t != s:
            p.write_text(t)
    for p, q in paths.items():
        q.parent.mkdir(exist_ok=True)
        p.rename(q)
    (r / "module-renames.json").write_text(json.dumps(renames, indent=2))
    (r / "certificate-declaration-renames.json").write_text(
        json.dumps(replacements, indent=2)
    )
    logger.info(
        "%s",
        {"modules": len(renames), "declarations_and_references": len(replacements)},
    )
