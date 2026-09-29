"""Wrap."""

import hashlib
import json
import logging
import re

from lean_pool.sofa_certificates.formatting import wrap_source

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    project = r / "pool/LeanPool/MovingSofa"
    identifiers = set()
    for p in project.rglob("*.lean"):
        identifiers.update(
            re.findall(
                "\\b[A-Za-z][A-Za-z0-9_]*_subtree_[A-Za-z0-9_]+\\b", p.read_text()
            )
        )
    renames = {
        n: "cover_subtree_" + hashlib.sha256(n.encode()).hexdigest()[:12]
        for n in identifiers
    }
    assert len(set(renames.values())) == len(renames)
    pattern = re.compile("\\b[A-Za-z][A-Za-z0-9_]*_subtree_[A-Za-z0-9_]+\\b")
    changes = []
    for p in project.rglob("*.lean"):
        s = p.read_text()
        t = pattern.sub(lambda m: renames[m[0]], s)
        for old, new in [
            ("if_pos", "ite_eq_left"),
            ("if_neg", "ite_eq_right"),
            ("dif_pos", "dite_eq_left"),
            ("dif_neg", "dite_eq_right"),
        ]:
            t = re.sub("\\b" + old + "\\b", new, t)
        t = t.replace("⟺", "↔")
        t = wrap_source(t)
        if t != s:
            p.write_text(t)
            changes.append(str(p.relative_to(r / "pool")))
    (r / "wrapping-repairs.json").write_text(
        json.dumps({"files": changes, "subtree_names": renames}, indent=2)
    )
    logger.info("%s %s %s", "Wrapped and normalized", len(changes), "files")
