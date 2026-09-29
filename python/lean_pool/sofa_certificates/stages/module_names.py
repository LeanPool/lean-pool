"""Module names."""

import json
import logging
import re

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    pool = r / "pool"
    project = pool / "LeanPool/MovingSofa"
    renames = {}
    paths = {}
    for p in project.rglob("*.lean"):
        if "_" not in p.stem:
            continue
        stem = "".join(x[:1].upper() + x[1:] for x in p.stem.split("_"))
        q = p.with_name(stem + ".lean")
        assert not q.exists()
        assert q not in paths.values()
        paths[p] = q
        renames[str(p.relative_to(pool).with_suffix("")).replace("/", ".")] = str(
            q.relative_to(pool).with_suffix("")
        ).replace("/", ".")
    pattern = re.compile("(?m)^(public import )(\\S+)$")
    for p in project.rglob("*.lean"):
        s = p.read_text()
        t = pattern.sub(lambda m: m[1] + renames.get(m[2], m[2]), s)
        if t != s:
            p.write_text(t)
    for p, q in paths.items():
        p.rename(q)
    d = json.loads((r / "module-renames.json").read_text())
    d = {k: renames.get(v, v) for k, v in d.items()}
    d.update(renames)
    (r / "module-renames.json").write_text(json.dumps(d, indent=2))
    logger.info("%s %s", "Additional renames", len(renames))
